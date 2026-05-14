import discord
from discord import app_commands
from discord.ext import commands
import wavelink
from wavelink.exceptions import NodeException
import asyncio
import itertools
import logging
import time
import random
import re as _re
import unicodedata as _unicodedata
import aiohttp
from typing import Iterable, Optional
from datetime import datetime, timezone
import playlist_manager
from topgg_utils import has_voted
from usage_manager import get_tier_from_message
from interaction_utils import safe_defer, send_interaction_message

logger = logging.getLogger(__name__)

VOTE_DURATION = 12 * 60 * 60
MIN_BITRATE_KBPS = 8
MAX_CONCURRENT_RESOLVES = 5
LYRICS_API_TIMEOUT_SECONDS = 12
MESSAGE_CHUNK_SIZE = 1900
MAX_REASONABLE_TRACK_MS = 24 * 60 * 60 * 1000

SOURCE_FAILURE_WINDOW_SECONDS = 45
MAX_CONSECUTIVE_SOURCE_FAILURES = 3
SOURCE_FAILOVER_SUPPRESS_SECONDS = 20
TRACK_END_ADVANCE_SUPPRESS_SECONDS = 5
SOURCE_NODE_BLOCK_SECONDS = 5 * 60
NODE_STOPPED_SUPPRESS_SECONDS = 12
AUTOPLAY_HISTORY_LIMIT = 3
TRACK_HISTORY_LIMIT = 20
RECENT_TRACKS_LIMIT = 5
CONTROL_FOLLOWUP_GRACE_SECONDS = 0.5
VC_CONNECT_TIMEOUT = 20.0
PLAYLIST_TRACKS_PER_PAGE = 10
MAX_PLAYLIST_SELECT_OPTIONS = 25

SOURCE_BLOCKED_MARKERS = (
    "requires login",
    "sign in to confirm",
    "confirm you're not a bot",
    "video is not available",
    "not available",
)

TIER_BITRATES_KBPS = {
    "basic": 64,
    "premium": 90,
    "gold": 112,
    "enterprise": 160,
}

LAVALINK_NODES = [
    {"uri": "http://n3.nexcloud.in:2026", "password": "nexcloud"},
    {"uri": "https://lava-v4.ajieblogs.eu.org:443", "password": "https://dsc.gg/ajidevserver"},
    {"uri": "https://lavalinkv4.serenetia.com:443", "password": "https://dsc.gg/ajidevserver"}
]


def _normalize_lavalink_uri(uri: str) -> str:
    uri = (uri or "").strip().rstrip("/")
    if not uri:
        raise ValueError("Lavalink URI is empty")
    if not uri.startswith(("http://", "https://")):
        uri = f"https://{uri}"
    return uri

_original_update_player = wavelink.Node._update_player
async def _patched_update_player(self, guild_id, /, *, data, replace=False):
    if "voice" in data and "channelId" not in data["voice"]:
        player = self._players.get(guild_id)
        if player and player.channel:
            data["voice"]["channelId"] = str(player.channel.id)
    try:
        return await asyncio.wait_for(
            _original_update_player(self, guild_id, data=data, replace=replace),
            timeout=10.0
        )
    except asyncio.TimeoutError:
        logger.warning("[TIMEOUT] Lavalink node %s timed out during update_player for guild %s", self.identifier, guild_id)
        raise
    except Exception as exc:
        if "session is closed" in str(exc).lower():
            logger.warning("[TIMEOUT] Lavalink node %s session closed for guild %s", self.identifier, guild_id)
        else:
            logger.error("[ERROR] Lavalink update_player failed for node %s, guild %s: %s", self.identifier, guild_id, exc)
        raise
wavelink.Node._update_player = _patched_update_player

_original_player_destroy = wavelink.Player._destroy
async def _patched_player_destroy(self, *args, **kwargs):
    try:
        return await _original_player_destroy(self, *args, **kwargs)
    except NodeException as exc:
        logger.warning("[DISCONNECT] Ignoring Lavalink destroy failure for stale player: %s", exc)
        return None
wavelink.Player._destroy = _patched_player_destroy

_VARIANT_WORDS = frozenset({
    "slowed", "sped", "reverb", "nightcore", "lofi", "lo-fi", "remix", "acoustic",
    "official", "video", "audio", "lyrics", "instrumental", "extended", "live",
    "cover", "edit", "version", "mix", "mashup", "flip", "remaster", "remastered",
    "feat", "ft", "prod", "bass", "boosted",
})
_STOP_WORDS = frozenset({"the", "a", "an", "in", "on", "at", "of", "and", "or", "is", "by"})


def _exception_text(exc: object) -> str:
    return str(exc or "").lower()


def _is_source_blocked_exception(exc: object) -> bool:
    text = _exception_text(exc)
    return any(marker in text for marker in SOURCE_BLOCKED_MARKERS)


def _looks_like_node_load_failure(exc: object) -> bool:
    text = _exception_text(exc)
    return (
        not text
        or text == "none"
        or "unexpected mimetype" in text
        or "failed to load tracks" in text
        or "something went wrong while looking up the track" in text
        or "502" in text
        or "bad gateway" in text
    )


def _sanitize_track_ms(ms: int | None) -> int:
    ms = int(ms or 0)
    if ms <= 0 or ms > MAX_REASONABLE_TRACK_MS:
        return 0
    return ms


def format_duration(ms: int | None, *, is_stream: bool = False) -> str:
    if is_stream:
        return "LIVE"
    ms = _sanitize_track_ms(ms)
    if ms == 0:
        return "?:??"
    seconds = ms // 1000
    minutes, seconds = divmod(seconds, 60)
    hours, minutes = divmod(minutes, 60)
    if hours:
        return f"{hours}:{minutes:02}:{seconds:02}"
    return f"{minutes}:{seconds:02}"


def make_progress_bar(position: int, duration: int, length: int = 20, *, is_stream: bool = False) -> str:
    if is_stream:
        return "▬" * length
    duration = _sanitize_track_ms(duration)
    if duration == 0:
        return "🔘" + "▬" * (length - 1)
    position = max(0, min(int(position or 0), duration))
    filled = max(0, min(int((position / duration) * length), length))
    return "▬" * filled + "🔘" + "▬" * (length - filled)


def _fmt_duration(seconds: int | None) -> str:
    if not seconds:
        return "0:00"
    m, s = divmod(int(seconds), 60)
    h, m = divmod(m, 60)
    return f"{h}:{m:02}:{s:02}" if h else f"{m}:{s:02}"


def _get_playlist_track_limit(tier: str) -> int | None:
    return {"basic": 20, "premium": 35, "gold": 60, "enterprise": None}.get((tier or "basic").lower(), 20)


def _get_playlist_count_limit(tier: str) -> int:
    return {"basic": 5, "premium": 20, "gold": 50, "enterprise": 100}.get((tier or "basic").lower(), 5)


def _playlist_owner_id(pl: dict) -> int:
    raw_owner = pl.get("uid") or pl.get("creator_id") or 0
    try:
        return int(raw_owner)
    except (TypeError, ValueError):
        return 0


def _get_target_bitrate(tier: str, voice_channel: discord.VoiceChannel | None = None) -> int:
    target = TIER_BITRATES_KBPS.get((tier or "basic").lower(), 64)
    if voice_channel and getattr(voice_channel, "bitrate", None):
        channel_kbps = max(int(voice_channel.bitrate) // 1000, MIN_BITRATE_KBPS)
        target = min(target, channel_kbps)
    return target


def _build_vote_embed() -> discord.Embed:
    embed = discord.Embed(
        title="🔒 Vote Required to Unlock This Feature",
        description=(
            "This music filter feature is locked behind a **free vote** on Top.gg!\n"
            "Vote once every 12 hours to unlock it. 💙"
        ),
        color=0x5865F2,
    )
    embed.add_field(
        name="⏱️ How It Works",
        value="1️⃣ Click **Vote Now** below\n2️⃣ Vote on Top.gg\n3️⃣ Feature unlocks for **12 hours** 🎉",
        inline=False,
    )
    embed.set_footer(text="🗳️ Voting is free and quick.")
    return embed


def _build_vote_view() -> discord.ui.View:
    view = discord.ui.View(timeout=None)
    view.add_item(discord.ui.Button(
        label="🗳️ Vote Now",
        url="https://top.gg/bot/1435987186502733878/vote",
        style=discord.ButtonStyle.link,
    ))
    return view


def _strip_accents(t: str) -> str:
    t = _unicodedata.normalize('NFKD', t)
    return ''.join(c for c in t if not _unicodedata.combining(c))


def _normalize_title(title: str) -> str:
    t = _strip_accents((title or "").lower().strip())
    t = _re.sub(r'[\(\[][^\)\]]*[\)\]]', '', t)
    t = _re.sub(
        r'\s*[-–-]?\s*\b(slowed|super slowed|sped up|reverb|nightcore|lofi|lo-fi|remix|acoustic|'
        r'official|video|audio|lyrics|feat|ft\.?|prod\.?|extended|instrumental)\b.*',
        '', t, flags=_re.IGNORECASE
    )
    return t.strip()


def _core_title(title: str) -> str:
    t = _strip_accents((title or "").lower().strip())
    return _re.split(r'\s*[\(\[（【]|\s+[-–-]\s+', t)[0].strip()


def _strip_artist_prefix(t: str) -> str:
    parts = _re.split(r'\s*[-–-]\s*', t, maxsplit=1)
    return parts[-1].strip() if len(parts) > 1 else t


def _strong_words(title: str) -> frozenset:
    t = _strip_accents((title or "").lower())
    t = _re.sub(r'[\(\[][^\)\]]*[\)\]]', '', t)
    words = _re.findall(r'[a-z0-9]+', t)
    return frozenset(w for w in words if len(w) >= 3 and w not in _STOP_WORDS and w not in _VARIANT_WORDS)


def _is_variant(title_a: str, title_b: str) -> bool:
    core_a, core_b = _core_title(title_a), _core_title(title_b)
    if core_a == core_b:
        return True
    words_a, words_b = _strong_words(title_a), _strong_words(title_b)
    if not words_a or not words_b:
        return False
    common = words_a & words_b
    overlap = len(common) / min(len(words_a), len(words_b))
    return overlap >= 0.6


def _is_duplicate(candidate: wavelink.Playable, history: list[dict], c_words: frozenset | None = None) -> bool:
    c_id  = getattr(candidate, 'identifier', None)
    c_uri = getattr(candidate, 'uri', None)
    c_dur = candidate.length or 0
    if c_words is None:
        c_words = _strong_words(candidate.title)
    c_core = _strip_artist_prefix(_core_title(candidate.title))
    for entry in history:
        if c_uri and entry.get('uri') and c_uri == entry['uri']:
            return True
        if c_id and entry.get('id') and c_id == entry['id']:
            return True
        old_core: str = entry.get('core', '')
        if old_core and c_core == old_core:
            return True
        if old_core and (c_core in old_core or old_core in c_core):
            return True
        if abs(c_dur - entry.get('dur', 0)) <= 7000 and c_words & entry.get('words', frozenset()):
            return True
    return False


def _build_control_rows(player: wavelink.Player):
    paused = player.paused
    volume = player.volume

    pause_resume = discord.ui.Button(
        label="Resume" if paused else "Pause",
        emoji="▶️" if paused else "⏸️",
        style=discord.ButtonStyle.success if paused else discord.ButtonStyle.secondary,
        custom_id="music:pause_resume",
    )
    previous_btn = discord.ui.Button(
        label="Previous", emoji="⏮️",
        style=discord.ButtonStyle.secondary, custom_id="music:previous",
    )
    skip_btn = discord.ui.Button(
        label="Forward", emoji="⏭️",
        style=discord.ButtonStyle.primary, custom_id="music:forward",
    )
    stop_btn = discord.ui.Button(
        label="Stop", emoji="⏹️",
        style=discord.ButtonStyle.danger, custom_id="music:stop",
    )
    playback_row = discord.ui.ActionRow()
    playback_row.add_item(previous_btn)
    playback_row.add_item(pause_resume)
    playback_row.add_item(skip_btn)
    playback_row.add_item(stop_btn)

    vol_down = discord.ui.Button(
        label="Vol −10", emoji="🔉",
        style=discord.ButtonStyle.secondary, custom_id="music:vol_down",
    )
    vol_label = discord.ui.Button(
        label=f"🔊 {volume}%", style=discord.ButtonStyle.secondary,
        custom_id="music:vol_label", disabled=True,
    )
    vol_up = discord.ui.Button(
        label="Vol +10", emoji="🔊",
        style=discord.ButtonStyle.secondary, custom_id="music:vol_up",
    )
    volume_row = discord.ui.ActionRow()
    volume_row.add_item(vol_down)
    volume_row.add_item(vol_label)
    volume_row.add_item(vol_up)

    return playback_row, volume_row, pause_resume, previous_btn, skip_btn, stop_btn, vol_down, vol_up


class MusicControlView(discord.ui.LayoutView):
    def __init__(self, cog: 'Music', player: wavelink.Player, *, timeout: Optional[float] = None):
        super().__init__(timeout=timeout)
        self.cog = cog
        self.player = player
        self._build()

    def _build(self) -> None:
        self._children.clear()  # type: ignore[attr-defined]
        track = self.player.current or getattr(self.player, "last_track", None)
        paused = self.player.paused
        volume = self.player.volume
        queue_size = self.player.queue.count

        if track:
            pos = self.player.position
            dur = track.length
            is_stream = getattr(track, "is_stream", False) or (not dur)
            track_text = (
                f"### {track.title}\n"
                f"-# by **{track.author}**\n"
                f"`{format_duration(pos, is_stream=is_stream)}` "
                f"{make_progress_bar(pos, dur, is_stream=is_stream)} "
                f"`{format_duration(dur, is_stream=is_stream)}`"
            )
            if paused:
                track_text = f"### ⏸️ (Paused) {track.title}\n-# by **{track.author}**"
        else:
            track_text = "### Nothing playing right now"

        status_icon = "⏸️" if paused else "▶️"
        footer_text = f"-# {status_icon}  Vol: **{volume}%**  •  Queue: **{queue_size}** track(s)  •  **Updates every 10 seconds**"

        playback_row, volume_row, pause_resume, previous_btn, skip_btn, stop_btn, vol_down, vol_up = _build_control_rows(self.player)
        pause_resume.callback = self.pause_resume_callback
        previous_btn.callback = self.previous_callback
        skip_btn.callback = self.forward_callback
        stop_btn.callback = self.stop_callback
        vol_down.callback = self.vol_down_callback
        vol_up.callback = self.vol_up_callback

        container = discord.ui.Container(
            discord.ui.TextDisplay(track_text),
            discord.ui.Separator(spacing=discord.SeparatorSpacing.small),
            playback_row,
            volume_row,
            discord.ui.Separator(spacing=discord.SeparatorSpacing.small),
            discord.ui.TextDisplay(footer_text),
            accent_colour=discord.Colour.blurple(),
        )
        self.add_item(container)

    def _refresh_player(self) -> None:
        
        gid = self.player.guild.id
        latest = self.cog._guild_players.get(gid)
        if latest and latest is not self.player:
            self.player = latest

    async def _check_author(self, interaction: discord.Interaction) -> bool:
        if not interaction.user.voice or interaction.user.voice.channel != self.player.channel:
            await send_interaction_message(interaction,
                "❌ You must be in the same voice channel to use controls.", ephemeral=True)
            return False
        return True

    async def _rebuild_and_edit(self, interaction: discord.Interaction) -> None:
        self._refresh_player()
        new_view = MusicControlView(self.cog, self.player)
        self.stop()
        if interaction.response.is_done():
            await interaction.edit_original_response(view=new_view)
        else:
            await interaction.response.edit_message(view=new_view)

    async def pause_resume_callback(self, interaction: discord.Interaction) -> None:
        await safe_defer(interaction)
        self._refresh_player()
        if not await self._check_author(interaction):
            return
        new_state = not self.player.paused
        await self.player.pause(new_state)
        self.player._last_progress_edit = time.monotonic()  # type: ignore[attr-defined]
        await asyncio.sleep(0.5)
        await self._rebuild_and_edit(interaction)

    async def previous_callback(self, interaction: discord.Interaction) -> None:
        await safe_defer(interaction)
        self._refresh_player()
        if not await self._check_author(interaction):
            return
        history: list[wavelink.Playable] = getattr(self.player, "_track_history", [])
        if len(history) < 2:
            if interaction.response.is_done():
                await interaction.followup.send("❌ No previous track.", ephemeral=True)
            else:
                await send_interaction_message(interaction, "❌ No previous track.", ephemeral=True)
            return
        if getattr(self.player, "_playlist_ctx", None):
            current_idx = getattr(self.player, "_playlist_track_idx", 0)
            self.player._playlist_track_idx = max(0, current_idx - 2)  # type: ignore[attr-defined]
        previous = history[-2]
        history.pop()
        history.pop()
        if self.player.current:
            self.player.queue.put_at(0, self.player.current)
        await self.player.play(previous)
        await asyncio.sleep(0.5)
        await self._rebuild_and_edit(interaction)

    async def forward_callback(self, interaction: discord.Interaction) -> None:
        await safe_defer(interaction)
        self._refresh_player()
        if not await self._check_author(interaction):
            return
        if self.player.queue.is_empty:
            if interaction.response.is_done():
                await interaction.followup.send("❌ No more tracks in the queue.", ephemeral=True)
            else:
                await send_interaction_message(interaction, "❌ No more tracks in the queue.", ephemeral=True)
            return
        next_track = self.player.queue.get()
        self.player.last_track = next_track  # type: ignore[attr-defined]
        await self.player.play(next_track)
        await asyncio.sleep(0.5)
        await self._rebuild_and_edit(interaction)

    async def stop_callback(self, interaction: discord.Interaction) -> None:
        await safe_defer(interaction)
        self._refresh_player()
        if not await self._check_author(interaction):
            return
        self.player._intentional_disconnect = True  # type: ignore[attr-defined]
        self.player.queue.clear()
        await self.player.stop()
        await self.cog._safe_disconnect_player(self.player, reason="control stop")
        stopped_view = discord.ui.LayoutView(timeout=None)
        stopped_view.add_item(discord.ui.Container(
            discord.ui.TextDisplay("### ⏹️  Playback stopped\n-# The bot has left the voice channel."),
            accent_colour=discord.Colour.red(),
        ))
        if interaction.response.is_done():
            await interaction.edit_original_response(view=stopped_view)
        else:
            await interaction.response.edit_message(view=stopped_view)

    async def vol_down_callback(self, interaction: discord.Interaction) -> None:
        await safe_defer(interaction)
        self._refresh_player()
        if not await self._check_author(interaction):
            return
        await self.player.set_volume(max(0, self.player.volume - 10))
        await self._rebuild_and_edit(interaction)

    async def vol_up_callback(self, interaction: discord.Interaction) -> None:
        await safe_defer(interaction)
        self._refresh_player()
        if not await self._check_author(interaction):
            return
        await self.player.set_volume(min(200, self.player.volume + 10))
        await self._rebuild_and_edit(interaction)


class PlaylistControlView(MusicControlView):
    def __init__(self, cog: 'Music', player: wavelink.Player, playlist_ctx: dict, *, timeout: Optional[float] = None):
        discord.ui.LayoutView.__init__(self, timeout=timeout)
        self.cog = cog
        self.player = player
        self.playlist_ctx = playlist_ctx
        self._build()

    def _build(self) -> None:
        self._children.clear()  # type: ignore[attr-defined]
        pl = self.playlist_ctx
        pl_name = pl.get("name", "Playlist")
        pl_creator = pl.get("creator_name", "Unknown")
        tracks = pl.get("tracks", [])
        tc = len(tracks)
        dur_secs = sum(t.get("duration") or 0 for t in tracks)
        track_idx = getattr(self.player, "_playlist_track_idx", 1)
        track = self.player.current
        paused = self.player.paused
        volume = self.player.volume
        queue_size = self.player.queue.count

        playlist_header = (
            f"### 〔 {pl_name} 〕\n"
            f"-# 👤 {pl_creator}  ·  🎵 {tc} tracks  ·  ⏱️ {_fmt_duration(dur_secs)}"
        )
        if track:
            pos = self.player.position
            dur = track.length
            is_stream = getattr(track, "is_stream", False) or (not dur)
            track_text = (
                f"-# ▸  NOW PLAYING  -  {track_idx} / {tc}\n"
                f"### {track.title}\n"
                f"-# by **{track.author}**\n"
                f"`{format_duration(pos, is_stream=is_stream)}` "
                f"{make_progress_bar(pos, dur, is_stream=is_stream)} "
                f"`{format_duration(dur, is_stream=is_stream)}`"
            )
        else:
            track_text = "### Nothing playing right now"

        status_icon = "⏸️" if paused else "▶️"
        footer_text = f"-# {status_icon}  Vol: **{volume}%**  ·  **{queue_size}** left in queue  ·  Updates every 10s"

        playback_row, volume_row, pause_resume, previous_btn, skip_btn, stop_btn, vol_down, vol_up = _build_control_rows(self.player)
        pause_resume.callback = self.pause_resume_callback
        previous_btn.callback = self.previous_callback
        skip_btn.callback = self.forward_callback
        stop_btn.callback = self.stop_callback
        vol_down.callback = self.vol_down_callback
        vol_up.callback = self.vol_up_callback

        container = discord.ui.Container(
            discord.ui.TextDisplay(playlist_header),
            discord.ui.Separator(spacing=discord.SeparatorSpacing.small),
            discord.ui.TextDisplay(track_text),
            discord.ui.Separator(spacing=discord.SeparatorSpacing.small),
            playback_row,
            volume_row,
            discord.ui.Separator(spacing=discord.SeparatorSpacing.small),
            discord.ui.TextDisplay(footer_text),
            accent_colour=discord.Colour.green(),
        )
        self.add_item(container)

    async def _rebuild_and_edit(self, interaction: discord.Interaction) -> None:
        new_view = PlaylistControlView(self.cog, self.player, self.playlist_ctx)
        self.stop()
        if interaction.response.is_done():
            await interaction.edit_original_response(view=new_view)
        else:
            await interaction.response.edit_message(view=new_view)


class PlaylistCreateModal(discord.ui.Modal, title="🎵 Create New Playlist"):
    name_field = discord.ui.TextInput(
        label="Playlist name",
        placeholder="e.g. Summer Vibes",
        max_length=50,
        required=True,
    )
    songs_field = discord.ui.TextInput(
        label="Songs - one per line (URL or search query)",
        style=discord.TextStyle.paragraph,
        placeholder=(
            "https://youtube.com/watch?v=...\n"
            "Blinding Lights The Weeknd\n"
            "Stay The Kid LAROI"
        ),
        max_length=2000,
        required=True,
    )

    def __init__(self, cog):
        super().__init__()
        self.cog = cog

    async def on_submit(self, interaction: discord.Interaction):
        if interaction.guild is None:
            await send_interaction_message(interaction, "❌ You can only use this command inside a server!", ephemeral=True)
            return
        name = self.name_field.value.strip()
        queries = [line.strip() for line in self.songs_field.value.splitlines() if line.strip()]
        if not queries:
            await send_interaction_message(interaction, "❌ No songs provided.", ephemeral=True)
            return
        tier = await get_tier_from_message(interaction)
        limit = _get_playlist_track_limit(tier)
        playlist_count_limit = _get_playlist_count_limit(tier)
        query_cap = len(queries) if limit is None else min(len(queries), limit)
        await interaction.response.defer()
        msg = await interaction.followup.send(
            content=f"🎵 Creating **{name}** - resolving {query_cap} song(s)…",
            wait=True,
        )
        pid, err = playlist_manager.create_playlist(
            interaction.guild.id, name, interaction.user.id,
            str(interaction.user), max_playlists=playlist_count_limit,
        )
        if err:
            await msg.edit(content=f"❌ {err}")
            return
        resolved = await self.cog._resolve_songs(queries[:query_cap], tier)
        added, skip = playlist_manager.add_tracks(interaction.guild.id, pid, resolved, max_tracks=limit)
        embed = discord.Embed(title="✅ Playlist Created", color=0x1DB954, timestamp=datetime.now(timezone.utc))
        embed.add_field(name="Name", value=name, inline=True)
        embed.add_field(name="Tracks added", value=str(added), inline=True)
        if skip:
            embed.add_field(name="Skipped", value=f"{skip} (limit reached)", inline=True)
        embed.add_field(
            name="How to play",
            value=f"Run `/playlist` → select **{name}** → press **▶️ Play**",
            inline=False,
        )
        limit_label = "unlimited" if limit is None else str(limit)
        embed.set_footer(text=f"Playlist ID: {pid} • max {limit_label} tracks")
        await msg.edit(content=None, embed=embed)


class PlaylistAddSongsModal(discord.ui.Modal):
    songs_field = discord.ui.TextInput(
        label="Songs - one per line (URL or search query)",
        style=discord.TextStyle.paragraph,
        placeholder="https://youtube.com/watch?v=...\nArtist – Song title",
        max_length=2000,
        required=True,
    )

    def __init__(self, cog, guild_id: int, playlist_id: str, playlist_name: str):
        modal_title_prefix = "Add Songs to "
        max_name_len = max(1, 45 - len(modal_title_prefix))
        super().__init__(title=f"{modal_title_prefix}{playlist_name[:max_name_len]}")
        self.cog = cog
        self.guild_id = guild_id
        self.playlist_id = playlist_id
        self.playlist_name = playlist_name

    async def on_submit(self, interaction: discord.Interaction):
        if interaction.guild is None:
            await send_interaction_message(interaction, "❌ You can only use this command inside a server!", ephemeral=True)
            return
        queries = [line.strip() for line in self.songs_field.value.splitlines() if line.strip()]
        if not queries:
            await send_interaction_message(interaction, "❌ No songs provided.", ephemeral=True)
            return
        pl = playlist_manager.get_playlist(self.guild_id, self.playlist_id)
        if not pl:
            await send_interaction_message(interaction, "❌ Playlist not found.", ephemeral=True)
            return
        tier = await get_tier_from_message(interaction)
        limit = _get_playlist_track_limit(tier)
        remaining = len(queries)
        if limit is not None:
            remaining = max(limit - len(pl.get("tracks", [])), 0)
        query_cap = min(len(queries), remaining)
        if query_cap <= 0:
            limit_label = "unlimited" if limit is None else str(limit)
            await send_interaction_message(interaction,
                f"❌ This playlist already reached your tier limit ({limit_label} tracks).",
                ephemeral=True,
            )
            return
        await interaction.response.defer()
        status = await interaction.followup.send(content=f"🔍 Resolving {query_cap} song(s)…", wait=True)
        resolved = await self.cog._resolve_songs(queries[:query_cap], tier)
        added, skip = playlist_manager.add_tracks(self.guild_id, self.playlist_id, resolved, max_tracks=limit)
        pl = playlist_manager.get_playlist(self.guild_id, self.playlist_id)
        embed = self.cog._build_playlist_manage_embed(pl, self.playlist_id)
        result_msg = (f"✅ Added **{added}** track(s) to **{self.playlist_name}**."
                    + (f"  {skip} skipped (limit reached)." if skip else ""))
        view = PlaylistManageView(self.cog, self.guild_id, interaction.user.id, self.playlist_id)
        await status.edit(content=result_msg, embed=embed, view=view)


def build_track_select_option(track: dict, index: int) -> discord.SelectOption:
    title = (track.get("title") or "Unknown title").strip()
    uploader = (track.get("uploader") or "Unknown uploader").strip()
    duration = _fmt_duration(track.get("duration"))
    label = f"{index + 1}. {title}"
    if len(label) > 100:
        label = f"{label[:97]}..."
    description = f"{uploader[:75]} · {duration}"[:100]
    return discord.SelectOption(label=label, value=str(index), description=description)


class PlaylistDeleteSongSelect(discord.ui.Select):
    def __init__(self, parent_view: "PlaylistDeleteTracksView"):
        self.parent_view = parent_view
        super().__init__(placeholder="Select a song to delete", options=[discord.SelectOption(label="Loading…", value="-1")])
        self.refresh_options()

    def refresh_options(self) -> None:
        pl = playlist_manager.get_playlist(self.parent_view.guild_id, self.parent_view.playlist_id)
        tracks = pl.get("tracks", []) if pl else []
        start = self.parent_view.page * PLAYLIST_TRACKS_PER_PAGE
        chunk = tracks[start:start + PLAYLIST_TRACKS_PER_PAGE]
        if not chunk:
            self.disabled = True
            self.options = [discord.SelectOption(label="No songs on this page", value="-1")]
            return
        self.disabled = False
        self.options = [build_track_select_option(track, start + i) for i, track in enumerate(chunk)]

    async def callback(self, interaction: discord.Interaction):
        try:
            idx = int(self.values[0])
        except (TypeError, ValueError):
            await send_interaction_message(interaction, "❌ Invalid song selection.", ephemeral=True)
            return
        await self.parent_view.delete_song(interaction, idx)


class PlaylistDeleteTracksView(discord.ui.View):
    def __init__(self, cog, guild_id: int, user_id: int, playlist_id: str, page: int = 0):
        super().__init__(timeout=None)
        self.cog = cog
        self.guild_id = guild_id
        self.user_id = user_id
        self.playlist_id = playlist_id
        self.page = page
        self.song_select = PlaylistDeleteSongSelect(self)
        self.add_item(self.song_select)

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.user_id:
            await send_interaction_message(interaction, "Not your command.", ephemeral=True)
            return False
        return True

    def _refresh_components(self) -> dict | None:
        pl = playlist_manager.get_playlist(self.guild_id, self.playlist_id)
        if not pl:
            return None
        total_pages = max(1, (len(pl.get("tracks", [])) + PLAYLIST_TRACKS_PER_PAGE - 1) // PLAYLIST_TRACKS_PER_PAGE)
        self.page = max(0, min(self.page, total_pages - 1))
        self.prev_btn.disabled = self.page <= 0
        self.next_btn.disabled = self.page >= total_pages - 1
        self.song_select.refresh_options()
        return pl

    async def delete_song(self, interaction: discord.Interaction, idx: int) -> None:
        if not playlist_manager.remove_track(self.guild_id, self.playlist_id, idx):
            await send_interaction_message(interaction, "❌ That song no longer exists.", ephemeral=True)
            return
        pl = self._refresh_components()
        if not pl:
            await interaction.response.edit_message(content="❌ Playlist not found.", embed=None, view=None)
            return
        if not pl.get("tracks"):
            embed = self.cog._build_playlist_manage_embed(pl, self.playlist_id)
            view = PlaylistManageView(self.cog, self.guild_id, self.user_id, self.playlist_id)
            await interaction.response.edit_message(content="✅ Song removed. Playlist is now empty.", embed=embed, view=view)
            return
        embed = self.cog._build_tracks_embed(pl, self.page)
        await interaction.response.edit_message(content="✅ Song removed.", embed=embed, view=self)

    @discord.ui.button(label="⬅️ Prev", style=discord.ButtonStyle.secondary)
    async def prev_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.page = max(0, self.page - 1)
        pl = self._refresh_components()
        if not pl:
            await interaction.response.edit_message(content="❌ Playlist not found.", embed=None, view=None)
            return
        embed = self.cog._build_tracks_embed(pl, self.page)
        await interaction.response.edit_message(embed=embed, view=self)

    @discord.ui.button(label="➡️ Next", style=discord.ButtonStyle.secondary)
    async def next_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.page += 1
        pl = self._refresh_components()
        if not pl:
            await interaction.response.edit_message(content="❌ Playlist not found.", embed=None, view=None)
            return
        embed = self.cog._build_tracks_embed(pl, self.page)
        await interaction.response.edit_message(embed=embed, view=self)

    @discord.ui.button(label="🔙 Back", style=discord.ButtonStyle.secondary)
    async def back_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        pl = playlist_manager.get_playlist(self.guild_id, self.playlist_id)
        if not pl:
            await interaction.response.edit_message(content="Playlist no longer exists.", embed=None, view=None)
            return
        embed = self.cog._build_playlist_manage_embed(pl, self.playlist_id)
        view = PlaylistManageView(self.cog, self.guild_id, self.user_id, self.playlist_id)
        await interaction.response.edit_message(content=None, embed=embed, view=view)


class PlaylistMoveSongSelect(discord.ui.Select):
    def __init__(self, parent_view: "PlaylistReorderTracksView"):
        self.parent_view = parent_view
        super().__init__(placeholder="Select a song to move", options=[discord.SelectOption(label="Loading…", value="-1")])
        self.refresh_options()

    def refresh_options(self) -> None:
        pl = playlist_manager.get_playlist(self.parent_view.guild_id, self.parent_view.playlist_id)
        tracks = pl.get("tracks", []) if pl else []
        start = self.parent_view.page * PLAYLIST_TRACKS_PER_PAGE
        chunk = tracks[start:start + PLAYLIST_TRACKS_PER_PAGE]
        if not chunk:
            self.disabled = True
            self.options = [discord.SelectOption(label="No songs on this page", value="-1")]
            return
        self.disabled = False
        self.options = [build_track_select_option(track, start + i) for i, track in enumerate(chunk)]
        if self.parent_view.selected_index is not None:
            self.placeholder = f"Selected: #{self.parent_view.selected_index + 1}"
        else:
            self.placeholder = "Select a song to move"

    async def callback(self, interaction: discord.Interaction):
        try:
            self.parent_view.selected_index = int(self.values[0])
        except (TypeError, ValueError):
            self.parent_view.selected_index = None
            await send_interaction_message(interaction, "❌ Invalid song selection.", ephemeral=True)
            return
        pl = self.parent_view._refresh_components()
        if not pl:
            await interaction.response.edit_message(content="❌ Playlist not found.", embed=None, view=None)
            return
        embed = self.parent_view.cog._build_tracks_embed(pl, self.parent_view.page)
        await interaction.response.edit_message(content=f"🎯 Selected song #{self.parent_view.selected_index + 1}.", embed=embed, view=self.parent_view)


class PlaylistReorderTracksView(discord.ui.View):
    def __init__(self, cog, guild_id: int, user_id: int, playlist_id: str, page: int = 0):
        super().__init__(timeout=None)
        self.cog = cog
        self.guild_id = guild_id
        self.user_id = user_id
        self.playlist_id = playlist_id
        self.page = page
        self.selected_index: int | None = None
        self.song_select = PlaylistMoveSongSelect(self)
        self.add_item(self.song_select)

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.user_id:
            await send_interaction_message(interaction, "Not your command.", ephemeral=True)
            return False
        return True

    def _refresh_components(self) -> dict | None:
        pl = playlist_manager.get_playlist(self.guild_id, self.playlist_id)
        if not pl:
            return None
        tracks = pl.get("tracks", [])
        total_pages = max(1, (len(tracks) + PLAYLIST_TRACKS_PER_PAGE - 1) // PLAYLIST_TRACKS_PER_PAGE)
        self.page = max(0, min(self.page, total_pages - 1))
        self.prev_btn.disabled = self.page <= 0
        self.next_btn.disabled = self.page >= total_pages - 1
        if self.selected_index is not None and not (0 <= self.selected_index < len(tracks)):
            self.selected_index = None
        can_move = self.selected_index is not None and len(tracks) > 1
        self.up_btn.disabled = not can_move or self.selected_index <= 0
        self.down_btn.disabled = not can_move or self.selected_index >= len(tracks) - 1
        self.top_btn.disabled = not can_move or self.selected_index <= 0
        self.bottom_btn.disabled = not can_move or self.selected_index >= len(tracks) - 1
        self.song_select.refresh_options()
        return pl

    async def _move_selected(self, interaction: discord.Interaction, target_index: int) -> None:
        pl = playlist_manager.get_playlist(self.guild_id, self.playlist_id)
        if not pl:
            await interaction.response.edit_message(content="❌ Playlist not found.", embed=None, view=None)
            return
        tracks = pl.get("tracks", [])
        if self.selected_index is None or not (0 <= self.selected_index < len(tracks)):
            await send_interaction_message(interaction, "❌ Select a song first.", ephemeral=True)
            return
        target_index = max(0, min(target_index, len(tracks) - 1))
        if target_index == self.selected_index:
            await send_interaction_message(interaction, "ℹ️ Song is already in that position.", ephemeral=True)
            return
        if not playlist_manager.move_track(self.guild_id, self.playlist_id, self.selected_index, target_index):
            await send_interaction_message(interaction, "❌ Could not update song order.", ephemeral=True)
            return
        self.selected_index = target_index
        self.page = target_index // PLAYLIST_TRACKS_PER_PAGE
        pl = self._refresh_components()
        if not pl:
            await interaction.response.edit_message(content="❌ Playlist not found.", embed=None, view=None)
            return
        embed = self.cog._build_tracks_embed(pl, self.page)
        await interaction.response.edit_message(content="✅ Song order updated.", embed=embed, view=self)

    @discord.ui.button(label="⬅️ Prev", style=discord.ButtonStyle.secondary)
    async def prev_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.page = max(0, self.page - 1)
        pl = self._refresh_components()
        if not pl:
            await interaction.response.edit_message(content="❌ Playlist not found.", embed=None, view=None)
            return
        embed = self.cog._build_tracks_embed(pl, self.page)
        await interaction.response.edit_message(embed=embed, view=self)

    @discord.ui.button(label="➡️ Next", style=discord.ButtonStyle.secondary)
    async def next_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.page += 1
        pl = self._refresh_components()
        if not pl:
            await interaction.response.edit_message(content="❌ Playlist not found.", embed=None, view=None)
            return
        embed = self.cog._build_tracks_embed(pl, self.page)
        await interaction.response.edit_message(embed=embed, view=self)

    @discord.ui.button(label="⬆️ Up", style=discord.ButtonStyle.secondary)
    async def up_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        idx = self.selected_index if self.selected_index is not None else 0
        await self._move_selected(interaction, idx - 1)

    @discord.ui.button(label="⬇️ Down", style=discord.ButtonStyle.secondary)
    async def down_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        idx = self.selected_index if self.selected_index is not None else 0
        await self._move_selected(interaction, idx + 1)

    @discord.ui.button(label="⏫ Top", style=discord.ButtonStyle.secondary)
    async def top_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self._move_selected(interaction, 0)

    @discord.ui.button(label="⏬ Bottom", style=discord.ButtonStyle.secondary)
    async def bottom_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self._move_selected(interaction, 10**9)

    @discord.ui.button(label="🔙 Back", style=discord.ButtonStyle.secondary)
    async def back_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        pl = playlist_manager.get_playlist(self.guild_id, self.playlist_id)
        if not pl:
            await interaction.response.edit_message(content="Playlist no longer exists.", embed=None, view=None)
            return
        embed = self.cog._build_playlist_manage_embed(pl, self.playlist_id)
        view = PlaylistManageView(self.cog, self.guild_id, self.user_id, self.playlist_id)
        await interaction.response.edit_message(content=None, embed=embed, view=view)


class PlaylistBrowserView(discord.ui.View):
    def __init__(self, cog, guild_id: int, user_id: int):
        super().__init__(timeout=None)
        self.cog = cog
        self.guild_id = guild_id
        self.user_id = user_id
        self._build_selects()

    def _playlist_options(self, playlists: Iterable[tuple[str, dict]]) -> list[discord.SelectOption]:
        options: list[discord.SelectOption] = []
        for pid, pl in itertools.islice(playlists, MAX_PLAYLIST_SELECT_OPTIONS):
            tc = len(pl.get("tracks", []))
            options.append(discord.SelectOption(
                label=pl["name"][:100],
                value=pid,
                description=f"{tc} track{'s' if tc != 1 else ''} · by {pl.get('creator_name', 'Unknown')[:40]}",
            ))
        return options

    def _build_dropdown(
        self,
        *,
        placeholder: str,
        custom_id: str,
        options: list[discord.SelectOption],
    ) -> discord.ui.Select:
        if options:
            select = discord.ui.Select(
                placeholder=placeholder,
                options=options,
                custom_id=custom_id,
            )
            select.callback = self.on_select
            return select
        empty = discord.ui.Select(
            placeholder=f"{placeholder} (none)",
            options=[discord.SelectOption(label="No playlists found", value="__none__")],
            custom_id=f"{custom_id}:empty",
            disabled=True,
        )
        return empty

    def _build_selects(self):
        for item in list(self.children):
            self.remove_item(item)
        playlists = playlist_manager.get_guild_playlists(self.guild_id)
        server_options = self._playlist_options(playlists.items())
        my_options = self._playlist_options(
            (pid, pl)
            for pid, pl in playlists.items()
            if _playlist_owner_id(pl) == self.user_id
        )
        self.add_item(self._build_dropdown(
            placeholder="My playlists",
            custom_id="playlist_browser:my",
            options=my_options,
        ))
        self.add_item(self._build_dropdown(
            placeholder="Playlists in this server",
            custom_id="playlist_browser:server",
            options=server_options,
        ))

    async def on_select(self, interaction: discord.Interaction):
        pid = interaction.data["values"][0]
        if pid == "__none__":
            await interaction.response.defer()
            return
        pl = playlist_manager.get_playlist(self.guild_id, pid)
        if not pl:
            await send_interaction_message(interaction, "❌ Playlist not found.", ephemeral=True)
            return
        embed = self.cog._build_playlist_manage_embed(pl, pid)
        view = PlaylistManageView(self.cog, self.guild_id, interaction.user.id, pid)
        await interaction.response.edit_message(embed=embed, view=view)


class PlaylistManageView(discord.ui.View):
    FIRST_TRACK_PAGE = 0

    def __init__(self, cog, guild_id: int, user_id: int, playlist_id: str):
        super().__init__(timeout=None)
        self.cog = cog
        self.guild_id = guild_id
        self.user_id = user_id
        self.playlist_id = playlist_id

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.user_id:
            await send_interaction_message(interaction, "Not your command.", ephemeral=True)
            return False
        return True

    @discord.ui.button(label="▶️ Play", style=discord.ButtonStyle.success, emoji="▶️")
    async def play_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.guild is None:
            await send_interaction_message(interaction, "❌ You can only use this command inside a server!", ephemeral=True)
            return
        if not interaction.user.voice or not interaction.user.voice.channel:
            await send_interaction_message(interaction, "❌ You need to jump into a voice channel first!", ephemeral=True)
            return
        pl = playlist_manager.get_playlist(self.guild_id, self.playlist_id)
        if not pl:
            await send_interaction_message(interaction, "❌ Playlist not found.", ephemeral=True)
            return
        tracks = pl.get("tracks", [])
        if not tracks:
            await send_interaction_message(interaction, "❌ This playlist is empty.", ephemeral=True)
            return
        await interaction.response.defer()
        voice_channel = interaction.user.voice.channel
        player: wavelink.Player = interaction.guild.voice_client
        try:
            if player is None or not player.connected:
                if player is not None:
                    await self.cog._safe_disconnect_player(player, reason="playlist stale cleanup")
                player = await self.cog._safe_connect(interaction.guild, voice_channel)
            elif player.channel != voice_channel:
                await interaction.followup.send(
                    f"❌ I'm already in {player.channel.mention}.", ephemeral=True
                )
                return
        except Exception as exc:
            logger.error("[PLAYLIST PLAY] Connect failed: %s", exc)
            await interaction.followup.send("❌ Failed to connect to your voice channel.", ephemeral=True)
            return
        player._text_channel = interaction.channel
        player._playlist_ctx = pl
        player._playlist_track_idx = 0
        player.queue.clear()
        loaded = 0
        for t in tracks:
            loaded_track = await self.cog._load_saved_playlist_track(t)
            if not loaded_track:
                logger.warning(
                    "[PLAYLIST PLAY] Could not load saved track '%s' (%s)",
                    t.get("title", "?"), t.get("web_url", "no-url"),
                )
                continue
            await player.queue.put_wait(loaded_track)
            loaded += 1
        if player.queue.is_empty:
            await interaction.followup.send("❌ Could not load any tracks from this playlist.", ephemeral=True)
            await self.cog._safe_disconnect_player(player, reason="empty saved playlist load")
            return
        first = player.queue.get()
        player.last_track = first
        try:
            await player.play(first)
            await asyncio.sleep(CONTROL_FOLLOWUP_GRACE_SECONDS)
            if not getattr(player, "_control_msg", None):
                view = PlaylistControlView(self.cog, player, pl)
                await self.cog._send_control_followup(player, view, interaction)
            skipped = len(tracks) - loaded
            suffix = f" ({skipped} track(s) skipped because Lavalink could not load them)." if skipped else ""
            await interaction.followup.send(f"▶️ Started playlist **{pl['name']}** with **{loaded}** loaded track(s).{suffix}")
        except Exception as exc:
            logger.error("[PLAYLIST PLAY] play() failed: %s", exc)
            failed_node = getattr(getattr(player, "node", None), "identifier", None)
            switched_player = await self.cog._switch_player_to_healthy_node(
                player,
                exclude={failed_node} if failed_node else None,
                reason="playlist initial play failure",
            )
            if switched_player is not None:
                try:
                    await switched_player.play(first)
                    await interaction.followup.send(f"▶️ Started playlist **{pl['name']}** after switching Lavalink nodes.")
                    return
                except Exception as retry_exc:
                    logger.error("[PLAYLIST PLAY] retry after node switch failed: %s", retry_exc)
            await interaction.followup.send("❌ Failed to start playback.", ephemeral=True)

    @discord.ui.button(label="➕ Add songs", style=discord.ButtonStyle.primary)
    async def add_songs_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        pl = playlist_manager.get_playlist(self.guild_id, self.playlist_id)
        if not pl:
            await send_interaction_message(interaction, "❌ Playlist not found.", ephemeral=True)
            return
        await interaction.response.send_modal(
            PlaylistAddSongsModal(self.cog, self.guild_id, self.playlist_id, pl["name"])
        )

    @discord.ui.button(label="➖ Remove songs", style=discord.ButtonStyle.danger)
    async def remove_songs_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        pl = playlist_manager.get_playlist(self.guild_id, self.playlist_id)
        if not pl:
            await send_interaction_message(interaction, "❌ Playlist not found.", ephemeral=True)
            return
        embed = self.cog._build_tracks_embed(pl, self.FIRST_TRACK_PAGE)
        view = PlaylistDeleteTracksView(
            self.cog, self.guild_id, self.user_id, self.playlist_id, self.FIRST_TRACK_PAGE
        )
        view._refresh_components()
        await interaction.response.edit_message(content="Select a song from the list to delete it.", embed=embed, view=view)

    @discord.ui.button(label="↕️ Edit order", style=discord.ButtonStyle.secondary)
    async def move_songs_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        pl = playlist_manager.get_playlist(self.guild_id, self.playlist_id)
        if not pl:
            await send_interaction_message(interaction, "❌ Playlist not found.", ephemeral=True)
            return
        if len(pl.get("tracks", [])) < 2:
            await send_interaction_message(interaction, "❌ Need at least 2 songs to reorder.", ephemeral=True)
            return
        embed = self.cog._build_tracks_embed(pl, self.FIRST_TRACK_PAGE)
        view = PlaylistReorderTracksView(
            self.cog, self.guild_id, self.user_id, self.playlist_id, self.FIRST_TRACK_PAGE
        )
        view._refresh_components()
        await interaction.response.edit_message(content="Select a song, then move it with the buttons.", embed=embed, view=view)

    @discord.ui.button(label="📋 View tracks", style=discord.ButtonStyle.secondary)
    async def view_tracks_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        pl = playlist_manager.get_playlist(self.guild_id, self.playlist_id)
        if not pl:
            await send_interaction_message(interaction, "❌ Playlist not found.", ephemeral=True)
            return
        embed = self.cog._build_tracks_embed(pl, 0)
        view = PlaylistTracksView(self.cog, self.guild_id, self.user_id, self.playlist_id, 0)
        await interaction.response.edit_message(embed=embed, view=view)

    @discord.ui.button(label="🗑️ Delete", style=discord.ButtonStyle.danger)
    async def delete_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        pl = playlist_manager.get_playlist(self.guild_id, self.playlist_id)
        if not pl:
            await send_interaction_message(interaction, "❌ Playlist not found.", ephemeral=True)
            return
        view = PlaylistConfirmDeleteView(self.cog, self.guild_id, self.user_id, self.playlist_id)
        await interaction.response.edit_message(
            content=f"⚠️ Are you sure you want to delete **{pl['name']}**?",
            embed=None,
            view=view,
        )


class PlaylistTracksView(discord.ui.View):
    TRACKS_PER_PAGE = PLAYLIST_TRACKS_PER_PAGE

    def __init__(self, cog, guild_id: int, user_id: int, playlist_id: str, page: int = 0):
        super().__init__(timeout=None)
        self.cog = cog
        self.guild_id = guild_id
        self.user_id = user_id
        self.playlist_id = playlist_id
        self.page = page

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.user_id:
            await send_interaction_message(interaction, "Not your command.", ephemeral=True)
            return False
        return True

    @discord.ui.button(label="⬅️ Prev", style=discord.ButtonStyle.secondary)
    async def prev_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        pl = playlist_manager.get_playlist(self.guild_id, self.playlist_id)
        if not pl:
            await send_interaction_message(interaction, "❌ Playlist not found.", ephemeral=True)
            return
        self.page = max(0, self.page - 1)
        embed = self.cog._build_tracks_embed(pl, self.page)
        await interaction.response.edit_message(embed=embed, view=self)

    @discord.ui.button(label="➡️ Next", style=discord.ButtonStyle.secondary)
    async def next_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        pl = playlist_manager.get_playlist(self.guild_id, self.playlist_id)
        if not pl:
            await send_interaction_message(interaction, "❌ Playlist not found.", ephemeral=True)
            return
        total_pages = max(1, (len(pl.get("tracks", [])) + self.TRACKS_PER_PAGE - 1) // self.TRACKS_PER_PAGE)
        self.page = min(total_pages - 1, self.page + 1)
        embed = self.cog._build_tracks_embed(pl, self.page)
        await interaction.response.edit_message(embed=embed, view=self)

    @discord.ui.button(label="➖ Remove song", style=discord.ButtonStyle.danger)
    async def remove_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        pl = playlist_manager.get_playlist(self.guild_id, self.playlist_id)
        if not pl:
            await send_interaction_message(interaction, "❌ Playlist not found.", ephemeral=True)
            return
        view = PlaylistDeleteTracksView(self.cog, self.guild_id, self.user_id, self.playlist_id, self.page)
        view._refresh_components()
        embed = self.cog._build_tracks_embed(pl, self.page)
        await interaction.response.edit_message(content="Select a song from the list to delete it.", embed=embed, view=view)

    @discord.ui.button(label="↕️ Move song", style=discord.ButtonStyle.secondary)
    async def move_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        pl = playlist_manager.get_playlist(self.guild_id, self.playlist_id)
        if not pl:
            await send_interaction_message(interaction, "❌ Playlist not found.", ephemeral=True)
            return
        if len(pl.get("tracks", [])) < 2:
            await send_interaction_message(interaction, "❌ Need at least 2 songs to reorder.", ephemeral=True)
            return
        view = PlaylistReorderTracksView(self.cog, self.guild_id, self.user_id, self.playlist_id, self.page)
        view._refresh_components()
        embed = self.cog._build_tracks_embed(pl, self.page)
        await interaction.response.edit_message(content="Select a song, then move it with the buttons.", embed=embed, view=view)

    @discord.ui.button(label="🔙 Back", style=discord.ButtonStyle.secondary)
    async def back_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        pl = playlist_manager.get_playlist(self.guild_id, self.playlist_id)
        if not pl:
            await send_interaction_message(interaction, "❌ Playlist not found.", ephemeral=True)
            return
        embed = self.cog._build_playlist_manage_embed(pl, self.playlist_id)
        view = PlaylistManageView(self.cog, self.guild_id, self.user_id, self.playlist_id)
        await interaction.response.edit_message(embed=embed, view=view)


class PlaylistConfirmDeleteView(discord.ui.View):
    def __init__(self, cog, guild_id: int, user_id: int, playlist_id: str):
        super().__init__(timeout=None)
        self.cog = cog
        self.guild_id = guild_id
        self.user_id = user_id
        self.playlist_id = playlist_id

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.user_id:
            await send_interaction_message(interaction, "Not your command.", ephemeral=True)
            return False
        return True

    @discord.ui.button(label="Yes, delete it", style=discord.ButtonStyle.danger, emoji="🗑️")
    async def confirm_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        pl = playlist_manager.get_playlist(self.guild_id, self.playlist_id)
        name = pl["name"] if pl else "Unknown"
        playlist_manager.delete_playlist(self.guild_id, self.playlist_id)
        await interaction.response.edit_message(content=f"🗑️ **{name}** has been deleted.", embed=None, view=None)

    @discord.ui.button(label="Cancel", style=discord.ButtonStyle.secondary)
    async def cancel_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        pl = playlist_manager.get_playlist(self.guild_id, self.playlist_id)
        if not pl:
            await interaction.response.edit_message(content="Playlist no longer exists.", embed=None, view=None)
            return
        embed = self.cog._build_playlist_manage_embed(pl, self.playlist_id)
        view = PlaylistManageView(self.cog, self.guild_id, self.user_id, self.playlist_id)
        await interaction.response.edit_message(embed=embed, view=view)


class Music(commands.Cog):
    def __init__(self, bot: commands.Bot):
        self.bot = bot
        self._history: dict[int, list[tuple[str, str, int]]] = {}
        self._autoplay: dict[int, bool] = {}
        self._autoplay_history: dict[int, list[dict]] = {}
        self._vote_unlocks: dict[int, float] = {}
        self._recovering_guilds: set[int] = set()
        self._processing_interactions: set[int] = set()
        self._guild_players: dict[int, wavelink.Player] = {}
        self._source_failure_bursts: dict[int, tuple[int, float]] = {}
        self._source_blocked_nodes: dict[str, float] = {}
        self._node_failures: dict[str, int] = {}
        self._node_last_failure: dict[str, float] = {}
        self._nodes_started = False
        self._node_init_lock = asyncio.Lock()
        self.bot.loop.create_task(self._memory_cleanup_loop())

    async def _memory_cleanup_loop(self) -> None:
        
        while not self.bot.is_closed():
            await asyncio.sleep(3600)  # Run every hour
            try:
                disconnected_gids: list[int] = []
                now_mono = time.monotonic()
                now_wall = time.time()
                for gid, p in self._guild_players.items():
                    if getattr(p, "_recovering", False):
                        continue
                    if getattr(p, "_intentional_disconnect", False):
                        continue
                    if p.playing or p.paused or p.connected:
                        continue
                    last_track_start = float(getattr(p, "_last_track_start", 0.0) or 0.0)
                    if last_track_start and (now_mono - last_track_start < 15):
                        continue
                    last_disconnect = float(getattr(p, "_last_voice_disconnect_at", 0.0) or 0.0)
                    if last_disconnect and (now_wall - last_disconnect < 15):
                        continue
                    last_active = float(getattr(p, "_last_active", 0.0) or 0.0) or last_track_start
                    if last_active and (now_mono - last_active > 600):
                        disconnected_gids.append(gid)
                for gid in disconnected_gids:
                    self._guild_players.pop(gid, None)
                    self._history.pop(gid, None)
                    self._autoplay_history.pop(gid, None)
                
                for gid in self._history:
                    if len(self._history[gid]) > RECENT_TRACKS_LIMIT:
                        self._history[gid] = self._history[gid][-RECENT_TRACKS_LIMIT:]
                
                if len(self._processing_interactions) > 100:
                    self._processing_interactions.clear()
                    
                logger.info("[RAM] Cleanup complete. Removed %d stale players.", len(disconnected_gids))
            except Exception as e:
                logger.error("[RAM] Cleanup failed: %s", e)

    async def _connect_lavalink_nodes_once(self) -> None:
        if self._nodes_started and wavelink.Pool.nodes:
            return
        async with self._node_init_lock:
            if self._nodes_started and wavelink.Pool.nodes:
                return
            shuffled_nodes = random.sample(LAVALINK_NODES, k=len(LAVALINK_NODES))
            nodes: list[wavelink.Node] = []
            for i, cfg in enumerate(shuffled_nodes):
                try:
                    uri = _normalize_lavalink_uri(cfg["uri"])
                except ValueError as exc:
                    logger.warning("Skipping invalid Lavalink node config %r: %s", cfg, exc)
                    continue
                nodes.append(wavelink.Node(
                    identifier=f"Node-{i}",
                    uri=uri,
                    password=cfg["password"],
                    resume_timeout=60,
                    inactive_player_timeout=None,
                    retries=3,
                ))
            if not nodes:
                logger.error("No valid Lavalink nodes available to connect.")
                return
            try:
                connected = await wavelink.Pool.connect(nodes=nodes, client=self.bot)
                self._nodes_started = True
                logger.info("Wavelink connected to %d node(s): %s", len(connected), list(connected.keys()))
            except Exception as exc:
                logger.error("Wavelink failed to connect: %s", exc)

    async def cog_load(self) -> None:
        await self._connect_lavalink_nodes_once()

    @commands.Cog.listener()
    async def on_wavelink_node_ready(self, payload: wavelink.NodeReadyEventPayload) -> None:
        logger.info("Wavelink node '%s' is ready (resumed=%s)", payload.node.identifier, payload.resumed)

    @commands.Cog.listener()
    async def on_wavelink_inactive_player(self, player: wavelink.Player) -> None:
        await self._safe_disconnect_player(player, reason="inactive player")

    async def _send_control_followup(
        self,
        player: wavelink.Player,
        view: discord.ui.LayoutView,
        interaction: discord.Interaction,
    ) -> bool:
        if interaction.is_expired():
            return False
        try:
            player._control_msg = await interaction.followup.send(  # type: ignore[attr-defined]
                content=None, view=view, wait=True,
            )
            return True
        except discord.HTTPException as exc:
            logger.warning("[CONTROL] Failed to send followup for guild %s: %s", player.guild.id, exc)
            player._control_msg = None  # type: ignore[attr-defined]
            return False

    async def _update_control_msg(self, player: wavelink.Player, view: discord.ui.LayoutView) -> bool:
        control_msg: discord.Message | None = getattr(player, "_control_msg", None)
        if control_msg:
            try:
                await control_msg.delete()
            except Exception:
                pass
            player._control_msg = None  # type: ignore[attr-defined]

        channel: discord.abc.Messageable | None = getattr(player, "_text_channel", None)
        if not channel:
            return False
        try:
            player._control_msg = await channel.send(content=None, view=view)  # type: ignore[attr-defined]
            return True
        except discord.Forbidden:
            player._text_channel = None  # type: ignore[attr-defined]
            player._control_msg = None  # type: ignore[attr-defined]
            return False
        except discord.HTTPException as exc:
            logger.warning("[CONTROL] Send failed for guild %s: %s", player.guild.id, exc)
            player._control_msg = None  # type: ignore[attr-defined]
            return False

    @commands.Cog.listener()
    async def on_wavelink_track_start(self, payload: wavelink.TrackStartEventPayload) -> None:
        player: wavelink.Player | None = payload.player
        if player is None:
            return
        logger.info("Now playing '%s' by %s - node=%s", payload.track.title, payload.track.author, player.node.identifier)
        player._last_track_start = time.monotonic()  # type: ignore[attr-defined]
        player._last_active = player._last_track_start  # type: ignore[attr-defined]
        player._active_node_id = getattr(player.node, "identifier", None)  # type: ignore[attr-defined]
        player._last_progress_edit = 0  # type: ignore[attr-defined]
        self._guild_players[player.guild.id] = player
        gid = player.guild.id
        self._clear_source_failures(gid)
        history = self._history.setdefault(gid, [])
        history.append((payload.track.title, payload.track.author, payload.track.length))
        if len(history) > RECENT_TRACKS_LIMIT:
            history.pop(0)
        track_history: list[wavelink.Playable] = getattr(player, "_track_history", [])
        track_history.append(payload.track)
        if len(track_history) > TRACK_HISTORY_LIMIT:
            track_history.pop(0)
        player._track_history = track_history  # type: ignore[attr-defined]
        ap_hist = self._autoplay_history.setdefault(gid, [])
        ap_hist.append({
            'id':    getattr(payload.track, 'identifier', None),
            'uri':   getattr(payload.track, 'uri', None),
            'core':  _strip_artist_prefix(_core_title(payload.track.title)),
            'dur':   payload.track.length or 0,
            'words': _strong_words(payload.track.title),
        })
        if len(ap_hist) > AUTOPLAY_HISTORY_LIMIT:
            del ap_hist[:-AUTOPLAY_HISTORY_LIMIT]
        playlist_ctx = getattr(player, "_playlist_ctx", None)
        if playlist_ctx:
            player._playlist_track_idx = getattr(player, "_playlist_track_idx", 0) + 1  # type: ignore[attr-defined]
            view: discord.ui.LayoutView = PlaylistControlView(self, player, playlist_ctx)
        else:
            view = MusicControlView(self, player)
        player._last_progress_edit = 0  # type: ignore[attr-defined]
        await self._update_control_msg(player, view)

    @commands.Cog.listener()
    async def on_wavelink_player_update(self, payload: wavelink.PlayerUpdateEventPayload) -> None:
        player: wavelink.Player | None = payload.player
        if player is None or (not player.playing and not player.paused):
            return
        now = time.monotonic()
        last = getattr(player, "_last_progress_edit", 0)
        if now - last < 10:
            return
        player._last_progress_edit = now  # type: ignore[attr-defined]
        control_msg: discord.Message | None = getattr(player, "_control_msg", None)
        if not control_msg:
            return
        try:
            playlist_ctx = getattr(player, "_playlist_ctx", None)
            refreshed_view: discord.ui.LayoutView = (
                PlaylistControlView(self, player, playlist_ctx) if playlist_ctx else MusicControlView(self, player)
            )
            await control_msg.edit(view=refreshed_view)
        except discord.HTTPException:
            pass

    @commands.Cog.listener()
    async def on_wavelink_track_stuck(self, payload: wavelink.TrackStuckEventPayload) -> None:
        player: wavelink.Player | None = payload.player
        if player is None:
            return
        logger.warning("[STUCK] Track '%s' stuck on node=%s - skipping.", getattr(payload.track, "title", "?"), player.node.identifier)
        await asyncio.sleep(1)
        if player.queue.count > 0:
            next_track = player.queue.get()
            player.last_track = next_track  # type: ignore[attr-defined]
            try:
                await player.play(next_track)
            except Exception as e:
                logger.error("[STUCK] play() failed after stuck: %s", e)
        else:
            control_msg: discord.Message | None = getattr(player, "_control_msg", None)
            if control_msg:
                try:
                    empty_view = discord.ui.LayoutView(timeout=None)
                    empty_view.add_item(discord.ui.Container(
                        discord.ui.TextDisplay("### ⚠️  Track got stuck\n-# Queue is empty."),
                        accent_colour=discord.Colour.orange(),
                    ))
                    await control_msg.edit(view=empty_view)
                except discord.HTTPException:
                    pass
                player._control_msg = None  # type: ignore[attr-defined]

    def _snapshot_playback(self, player: wavelink.Player) -> None:
        try:
            player._playback_snapshot = {  # type: ignore[attr-defined]
                "current": player.current or getattr(player, "last_track", None),
                "queue": list(player.queue) if not player.queue.is_empty else [],
                "position": int(getattr(player, "position", 0) or 0),
                "volume": int(getattr(player, "volume", 100) or 100),
                "paused": bool(getattr(player, "paused", False)),
                "loop": getattr(player.queue, "mode", wavelink.QueueMode.normal),
            }
        except Exception:
            pass

    async def _guild_recovery_controller(self, player: wavelink.Player, *, reason: str, exclude: set[str] | None = None) -> wavelink.Player | None:
        gid = player.guild.id
        if gid in self._recovering_guilds:
            return None
        return await self._switch_player_to_healthy_node(player, exclude=exclude, reason=reason)

    def _record_source_failure(self, guild_id: int) -> int:
        now = time.time()
        count, started = self._source_failure_bursts.get(guild_id, (0, now))
        if now - started > SOURCE_FAILURE_WINDOW_SECONDS:
            count, started = 0, now
        count += 1
        self._source_failure_bursts[guild_id] = (count, started)
        return count

    def _clear_source_failures(self, guild_id: int) -> None:
        self._source_failure_bursts.pop(guild_id, None)

    async def _switch_player_to_healthy_node(
        self,
        player: wavelink.Player,
        *,
        exclude: set[str] | None = None,
        reason: str = "recovery",
    ) -> wavelink.Player | None:
        voice_channel = player.channel
        gid = player.guild.id
        
        if gid in self._recovering_guilds and "hard recovery" not in reason.lower():
            logger.warning("[RECOVERY] Recovery already in progress for guild %s, skipping %s.", gid, reason)
            return None
            
        if not voice_channel:
            logger.error("[RECOVERY] No voice channel for guild %s during %s.", gid, reason)
            return None

        self._recovering_guilds.add(gid)
        try:
            target_volume = max(0, min(200, int(getattr(player, "volume", 100))))
            snap = getattr(player, "_playback_snapshot", None) or {}
            queued_tracks = list(snap.get("queue") or ([] if player.queue.is_empty else list(player.queue)))
            current_snapshot = snap.get("current")
            if current_snapshot is not None:
                queued_tracks = [t for t in queued_tracks if t != current_snapshot]
            attrs_to_copy = (
                "_text_channel", "_control_msg", "_playlist_ctx",
                "_playlist_track_idx", "_track_history", "_last_progress_edit", "last_track",
                "_autoplay", "_loop_mode"
            )
            copied_state = {attr: getattr(player, attr, None) for attr in attrs_to_copy}
            
            player._recovering = True  # type: ignore[attr-defined]
            player._transitioning = True  # type: ignore[attr-defined]
            
            healthy_nodes = self._healthy_connect_nodes(exclude=exclude)
            if not healthy_nodes:
                logger.error("[RECOVERY] No healthy nodes available to reconnect guild %s", gid)
                return None

            for node in healthy_nodes:
                try:
                    logger.warning("[RECOVERY] Reconnecting guild %s on node %s after %s.", gid, node.identifier, reason)
                    new_player = await self._safe_connect(player.guild, voice_channel, nodes=[node])
                    
                    for attr, value in copied_state.items():
                        if value is not None:
                            setattr(new_player, attr, value)  # type: ignore[attr-defined]
                    
                    new_player._suppress_failover_until = time.time() + SOURCE_FAILOVER_SUPPRESS_SECONDS  # type: ignore[attr-defined]
                    new_player._active_node_id = node.identifier  # type: ignore[attr-defined]
                    if queued_tracks:
                        await new_player.queue.put_wait(queued_tracks)
                    if snap.get("loop") is not None:
                        new_player.queue.mode = snap.get("loop")
                    await new_player.set_volume(int(snap.get("volume", target_volume)))
                    if bool(snap.get("paused", False)):
                        await new_player.pause(True)
                    
                    new_player._recovering = False  # type: ignore[attr-defined]
                    new_player._transitioning = False  # type: ignore[attr-defined]
                    new_player._intentional_disconnect = False  # type: ignore[attr-defined]
                    player._recovering = False  # type: ignore[attr-defined]
                    player._transitioning = False  # type: ignore[attr-defined]
                    self._snapshot_playback(new_player)
                    await asyncio.sleep(5)
                    self._recovering_guilds.discard(gid)
                    return new_player
                except Exception as exc:
                    logger.error("[RECOVERY] Reconnect on node %s failed for guild %s: %s", node.identifier, gid, exc)
                    self._node_failures[node.identifier] = self._node_failures.get(node.identifier, 0) + 1
                    self._node_last_failure[node.identifier] = time.time()
                    if isinstance(exc, asyncio.TimeoutError) or "timeout" in str(exc).lower():
                        self._source_blocked_nodes[node.identifier] = time.time() + (SOURCE_NODE_BLOCK_SECONDS * 2)
            
            logger.error("[RECOVERY] All healthy nodes exhausted for guild %s after %s.", gid, reason)
            return None
        finally:
            player._recovering = False  # type: ignore[attr-defined]
            player._transitioning = False  # type: ignore[attr-defined]
            player._intentional_disconnect = False  # type: ignore[attr-defined]
            self._recovering_guilds.discard(gid)

    async def _abort_unplayable_source_burst(self, player: wavelink.Player, reason_text: str) -> None:
        gid = player.guild.id
        logger.error("[SOURCE] Too many source-level failures for guild %s; aborting. Last error: %s", gid, reason_text)
        try:
            player.queue.clear()
        except Exception:
            pass
        control_msg: discord.Message | None = getattr(player, "_control_msg", None)
        if control_msg:
            try:
                error_view = discord.ui.LayoutView(timeout=None)
                error_view.add_item(discord.ui.Container(
                    discord.ui.TextDisplay(
                        "### ❌  Playback source is blocking these tracks\n"
                        "-# YouTube login/bot-check errors on this Lavalink node. "
                        "Try a direct URL or wait and retry."
                    ),
                    accent_colour=discord.Colour.red(),
                ))
                await control_msg.edit(view=error_view)
            except discord.HTTPException:
                pass
            player._control_msg = None  # type: ignore[attr-defined]
        player._intentional_disconnect = True  # type: ignore[attr-defined]
        player._suppress_failover_until = time.time() + SOURCE_FAILOVER_SUPPRESS_SECONDS  # type: ignore[attr-defined]
        self._guild_players.pop(gid, None)
        self._autoplay_history.pop(gid, None)
        self._clear_source_failures(gid)
        await self._safe_disconnect_player(player, reason="source failure abort")

    @commands.Cog.listener()
    async def on_wavelink_track_exception(self, payload: wavelink.TrackExceptionEventPayload) -> None:
        player: wavelink.Player | None = payload.player
        if player is None:
            return
        active_node = getattr(player, "_active_node_id", None)
        if active_node and player.node.identifier != active_node:
            logger.debug("[EXCEPTION] Ignoring stale node event from %s (active=%s).", player.node.identifier, active_node)
            return
            
        exc = getattr(payload, "exception", "unknown")
        is_source_blocked = _is_source_blocked_exception(exc)
        track = payload.track
        logger.warning("[EXCEPTION] Track '%s' failed on node=%s. Error: %s",
            getattr(track, "title", "?"), player.node.identifier, exc)
            
        gid = player.guild.id
        failed_node_id = player.node.identifier

        if is_source_blocked:
            now = time.time()
            self._source_blocked_nodes[failed_node_id] = now + SOURCE_NODE_BLOCK_SECONDS
            logger.warning("[SOURCE] Node %s blocked by YouTube. Attempting failover for '%s'...", failed_node_id, track.title)
            
            switched_player = await self._switch_player_to_healthy_node(
                player,
                exclude={failed_node_id},
                reason="source blocked failover"
            )
            
            if switched_player:
                try:
                    logger.info("[FAILOVER] Re-attempting '%s' on node %s", track.title, switched_player.node.identifier)
                    await switched_player.play(track)
                    return # Successfully re-started on a new node
                except Exception as retry_exc:
                    logger.error("[FAILOVER] Re-attempt on node %s failed: %s", switched_player.node.identifier, retry_exc)
            else:
                logger.error("[FAILOVER] No alternative nodes available to replay '%s'", track.title)

        if player.queue.count > 0:
            next_track = player.queue.get()
            player.last_track = next_track  # type: ignore[attr-defined]
            player._suppress_track_end_advance_until = time.time() + TRACK_END_ADVANCE_SUPPRESS_SECONDS  # type: ignore[attr-defined]
            try:
                await player.play(next_track)
            except Exception as play_exc:
                logger.error("[EXCEPTION] Failed to start next track: %s", play_exc)
        else:
            control_msg: discord.Message | None = getattr(player, "_control_msg", None)
            if control_msg:
                try:
                    empty_view = discord.ui.LayoutView(timeout=None)
                    empty_view.add_item(discord.ui.Container(
                        discord.ui.TextDisplay("### ❌  Track failed\n-# Queue is empty."),
                        accent_colour=discord.Colour.red(),
                    ))
                    await control_msg.edit(view=empty_view)
                except discord.HTTPException:
                    pass
                player._control_msg = None  # type: ignore[attr-defined]

    async def _ensure_music_control(self, interaction: discord.Interaction) -> wavelink.Player | None:
        if interaction.guild is None:
            await send_interaction_message(interaction, "❌ This can only be used in a server.", ephemeral=True)
            return None
        if not interaction.user.voice or not interaction.user.voice.channel:  # type: ignore[union-attr]
            await send_interaction_message(interaction, "❌ You need to jump into a voice channel first!", ephemeral=True)
            return None
        player: wavelink.Player = interaction.guild.voice_client  # type: ignore[assignment]
        if player is None or not isinstance(player, wavelink.Player):
            await send_interaction_message(interaction, "❌ The bot is not connected.", ephemeral=True)
            return None
        if interaction.user.voice.channel != player.channel:  # type: ignore[union-attr]
            await send_interaction_message(interaction, "❌ You need to be in the same voice channel as me to do that!", ephemeral=True)
            return None
        return player

    async def _check_vote_status(self, user_id: int) -> bool:
        now = time.time()
        expired_unlocks = [
            uid for uid, unlocked_at in self._vote_unlocks.items()
            if (now - unlocked_at) >= VOTE_DURATION
        ]
        for uid in expired_unlocks:
            self._vote_unlocks.pop(uid, None)
        unlock_time = self._vote_unlocks.get(user_id)
        if unlock_time and (now - unlock_time) < VOTE_DURATION:
            return True
        if await has_voted(user_id):
            self._vote_unlocks[user_id] = now
            return True
        return False

    async def _require_vote_slash(self, interaction: discord.Interaction) -> bool:
        voted = await self._check_vote_status(interaction.user.id)
        if not voted:
            await send_interaction_message(interaction, embed=_build_vote_embed(), view=_build_vote_view(), ephemeral=False)
        return voted


    def _mark_node_load_failed(self, node: wavelink.Node, exc: object) -> None:
        self._node_failures[node.identifier] = self._node_failures.get(node.identifier, 0) + 1
        self._node_last_failure[node.identifier] = time.time()
        if _looks_like_node_load_failure(exc) or _is_source_blocked_exception(exc):
            self._source_blocked_nodes[node.identifier] = time.time() + SOURCE_NODE_BLOCK_SECONDS
            logger.warning(
                "[SAFE_SEARCH] Temporarily blocked Lavalink node %s for load/search failures: %s",
                node.identifier, exc,
            )

    async def _safe_disconnect_player(self, player: wavelink.Player | None, *, reason: str = "cleanup") -> None:
        if player is None:
            return
        try:
            await player.disconnect()
        except NodeException as exc:
            logger.warning("[DISCONNECT] Lavalink destroy failed during %s, ignoring stale player: %s", reason, exc)
        except Exception as exc:
            logger.warning("[DISCONNECT] Voice disconnect failed during %s: %s", reason, exc)

    async def _load_saved_playlist_track(self, track_data: dict) -> wavelink.Playable | wavelink.Playlist | None:
        url = (track_data.get("web_url") or "").strip()
        title = (track_data.get("title") or "").strip()
        uploader = (track_data.get("uploader") or "").strip()
        queries: list[str] = []
        if title:
            query_text = f"{title} {uploader}".strip()
            queries.append(f"ytmsearch:{query_text}")
            queries.append(f"ytsearch:{query_text}")
        if url:
            queries.append(url)
        for query in dict.fromkeys(q for q in queries if q):
            try:
                results = await self._safe_search(query)
            except Exception as exc:
                logger.warning("[PLAYLIST PLAY] Saved track query failed for %r: %s", query, exc)
                continue
            if not results:
                continue
            if isinstance(results, wavelink.Playlist):
                return results
            return results[0]
        return None

    def _healthy_connect_nodes(self, *, exclude: set[str] | None = None) -> list[wavelink.Node]:
        now = time.time()
        exclude = exclude or set()
        cooldown_seconds = SOURCE_NODE_BLOCK_SECONDS
        expired = [node_id for node_id, until in self._source_blocked_nodes.items() if until <= now]
        for node_id in expired:
            self._source_blocked_nodes.pop(node_id, None)
        return [
            node
            for node in wavelink.Pool.nodes.values()
            if node.status == wavelink.NodeStatus.CONNECTED
            and node.identifier not in exclude
            and self._source_blocked_nodes.get(node.identifier, 0) <= now
            and (
                self._node_failures.get(node.identifier, 0) < 3
                or (now - self._node_last_failure.get(node.identifier, 0)) >= cooldown_seconds
            )
        ]

    async def _safe_connect(
        self,
        guild: discord.Guild,
        channel: discord.VoiceChannel,
        *,
        nodes: list[wavelink.Node] | None = None,
    ) -> wavelink.Player:
        existing_player = guild.voice_client
        if isinstance(existing_player, wavelink.Player) and existing_player.connected and existing_player.channel == channel:
            self._guild_players[guild.id] = existing_player
            return existing_player
        if isinstance(existing_player, wavelink.Player):
            existing_player._intentional_disconnect = True  # type: ignore[attr-defined]
            await self._safe_disconnect_player(existing_player, reason="safe_connect replace existing player")
            self._guild_players.pop(guild.id, None)
        if guild.me.voice:
            logger.warning("[CONNECT] Stale voice state for guild %s - clearing before reconnect.", guild.id)
            try:
                await guild.change_voice_state(channel=None)
            except Exception as exc:
                logger.warning("[CONNECT] Failed to clear stale guild voice state for %s: %s", guild.id, exc)
        connect_nodes = nodes if nodes is not None else self._healthy_connect_nodes()
        if not connect_nodes:
            connect_nodes = [
                node for node in wavelink.Pool.nodes.values()
                if node.status == wavelink.NodeStatus.CONNECTED
            ]
        def _player_factory(client: discord.Client, voice_channel: discord.abc.Connectable) -> wavelink.Player:
            pl = wavelink.Player(client, voice_channel, nodes=connect_nodes or None)
            pl.queue_lock = asyncio.Lock()  # type: ignore[attr-defined]
            pl._transitioning = False  # type: ignore[attr-defined]
            pl._intentional_disconnect = False  # type: ignore[attr-defined]
            pl._recovering = False  # type: ignore[attr-defined]
            pl._last_voice_disconnect_at = 0.0  # type: ignore[attr-defined]
            return pl
        player = await channel.connect(cls=_player_factory, self_deaf=True, reconnect=True, timeout=VC_CONNECT_TIMEOUT)
        self._guild_players[guild.id] = player
        return player

    async def _safe_search(self, query: str) -> Optional[wavelink.Search]:
        healthy_nodes = self._healthy_connect_nodes()
        nodes_to_try = healthy_nodes or [
            node for node in wavelink.Pool.nodes.values()
            if node.status == wavelink.NodeStatus.CONNECTED
        ]

        for node in nodes_to_try:
            try:
                tracks: wavelink.Search = await wavelink.Pool.fetch_tracks(query, node=node)
                if tracks:
                    return tracks
            except Exception as exc:
                logger.warning("[SAFE_SEARCH] Node %s failed for %r: %s", node.identifier, query, exc)
                self._mark_node_load_failed(node, exc)

        logger.error("[SAFE_SEARCH] All nodes exhausted for query: %r", query)
        return None

    async def _apply_named_filter(self, player: wavelink.Player, preset: str):
        if preset in {"reset", "normal"}:
            await player.set_filters(None)
            return
        filters = wavelink.Filters()
        if preset == "bassboost":
            filters.equalizer.set(bands=[
                {"band": 0, "gain": 0.3}, {"band": 1, "gain": 0.25},
                {"band": 2, "gain": 0.2}, {"band": 3, "gain": 0.15},
                {"band": 4, "gain": 0.1}, {"band": 5, "gain": 0.0},
                *[{"band": n, "gain": -0.05} for n in range(6, 15)],
            ])
        elif preset == "nightcore":
            filters.timescale.set(speed=1.15, pitch=1.15, rate=1.0)
        elif preset == "slow":
            filters.timescale.set(speed=0.85, pitch=0.9, rate=1.0)
        elif preset == "8d":
            filters.rotation.set(rotation_hz=0.2)
            filters.channel_mix.set(left_to_left=0.5, left_to_right=0.5, right_to_left=0.5, right_to_right=0.5)
        elif preset == "treble":
            filters.equalizer.set(bands=[{"band": n, "gain": (0.2 if n >= 10 else 0.0)} for n in range(15)])
        elif preset == "lofi":
            filters.timescale.set(speed=0.92, pitch=0.92, rate=1.0)
            filters.low_pass.set(smoothing=20.0)
        elif preset == "vaporwave":
            filters.timescale.set(speed=0.8, pitch=0.8, rate=1.0)
        await player.set_filters(filters)

    async def _resolve_songs(self, queries: list[str], tier: str) -> list[dict]:
        sem = asyncio.Semaphore(MAX_CONCURRENT_RESOLVES)
        async def _one(q: str) -> Optional[dict]:
            async with sem:
                try:
                    results = await self._safe_search(q)
                    if not results or isinstance(results, wavelink.Playlist):
                        return None
                    track = results[0]
                    return {
                        "title": track.title or q,
                        "uploader": track.author or "Unknown",
                        "duration": (track.length // 1000 if track.length else 0),
                        "web_url": track.uri,
                    }
                except Exception as exc:
                    logger.warning("[PLAYLIST RESOLVE] %r: %s", q, exc)
                    return None
        raw = await asyncio.gather(*[_one(q) for q in queries], return_exceptions=True)
        return [r for r in raw if isinstance(r, dict) and r]

    def _build_playlist_browser_embed(self, guild_id: int, user_id: int) -> discord.Embed:
        playlists = playlist_manager.get_guild_playlists(guild_id)
        server_count = len(playlists)
        my_count = sum(
            1
            for pl in playlists.values()
            if _playlist_owner_id(pl) == user_id
        )
        embed = discord.Embed(title="🎵 Server Playlists", color=0x1DB954, timestamp=datetime.now(timezone.utc))
        if not playlists:
            embed.description = "No playlists yet. Use `/playlistcreate` to make one."
            return embed
        embed.description = (
            f"**{server_count}** playlist{'s' if server_count != 1 else ''} saved in this server\n"
            f"**{my_count}** in My playlists"
        )
        embed.set_footer(text="Use the My playlists / Playlists in this server dropdowns below")
        return embed

    def _build_playlist_manage_embed(self, pl: dict, playlist_id: str) -> discord.Embed:
        tracks = pl.get("tracks", [])
        tc = len(tracks)
        dur_secs = sum(t.get("duration") or 0 for t in tracks)
        embed = discord.Embed(title=f"🎵 {pl['name']}", color=0x1DB954, timestamp=datetime.now(timezone.utc))
        embed.description = f"Created by **{pl['creator_name']}**"
        embed.add_field(name="Tracks", value=str(tc), inline=True)
        embed.add_field(name="Duration", value=_fmt_duration(dur_secs), inline=True)
        embed.add_field(name="ID", value=playlist_id, inline=True)
        if tracks:
            preview = []
            for i, t in enumerate(tracks[:5], 1):
                d = _fmt_duration(t.get("duration"))
                preview.append(f"`{i}.` {t.get('title','?')} - {t.get('uploader','?')} `{d}`")
            if tc > 5:
                preview.append(f"*… and {tc-5} more*")
            embed.add_field(name="Tracks preview", value="\n".join(preview), inline=False)
        embed.set_footer(text="Use the buttons below to play, edit, or delete")
        return embed

    def _build_tracks_embed(self, pl: dict, page: int) -> discord.Embed:
        tracks = pl.get("tracks", [])
        total = len(tracks)
        per_p = PlaylistTracksView.TRACKS_PER_PAGE
        pages = max(1, (total + per_p - 1) // per_p)
        page = max(0, min(page, pages - 1))
        start = page * per_p
        chunk = tracks[start:start + per_p]
        dur_all = sum(t.get("duration") or 0 for t in tracks)
        embed = discord.Embed(title=f"📋 {pl['name']} - Track list", color=0x1DB954, timestamp=datetime.now(timezone.utc))
        embed.description = f"Page {page+1} of {pages} · {total} tracks total · {_fmt_duration(dur_all)}"
        lines = []
        for i, t in enumerate(chunk, start + 1):
            d = _fmt_duration(t.get("duration"))
            lines.append(f"`{i:>2}.` **{t.get('title','?')}**\n      {t.get('uploader','?')} · `{d}`")
        embed.add_field(name="\u200b", value="\n".join(lines) or "Empty", inline=False)
        embed.set_footer(text=f"Total: {_fmt_duration(dur_all)} · {total} tracks")
        return embed

    async def _run_filter_command(self, interaction: discord.Interaction, *, preset: str, name: str, emoji: str) -> None:
        if not await self._require_vote_slash(interaction):
            return
        player = await self._ensure_music_control(interaction)
        if player is None:
            return
        await self._apply_named_filter(player, preset)
        await send_interaction_message(interaction, f"{emoji} Applied **{name}** filter.", ephemeral=True)

    @app_commands.command(name="play", description="Search for a song and play it in your voice channel")
    @app_commands.describe(query="Song title, artist, or URL")
    async def play(self, interaction: discord.Interaction, query: str) -> None:
        if not interaction.user.voice or not interaction.user.voice.channel:  # type: ignore[union-attr]
            await send_interaction_message(interaction, "❌ You need to be in a voice channel first.", ephemeral=True)
            return
        if not await self._require_vote_slash(interaction):
            return
        if interaction.id in self._processing_interactions:
            return
        self._processing_interactions.add(interaction.id)
        try:
            await interaction.response.defer(thinking=True)
        except discord.HTTPException:
            pass
        try:
            voice_channel = interaction.user.voice.channel  # type: ignore[union-attr]
            player: wavelink.Player = interaction.guild.voice_client  # type: ignore[assignment]
            we_connected = False
            if player is None or not player.connected:
                if player is not None and not player.connected:
                    logger.warning("[PLAY] Zombie player for guild %s - clearing.", interaction.guild.id)
                    self._guild_players.pop(interaction.guild.id, None)
                    await self._safe_disconnect_player(player, reason="play zombie cleanup")
                try:
                    player = await self._safe_connect(interaction.guild, voice_channel)
                    we_connected = True
                except Exception as exc:
                    logger.error("[PLAY] Failed to connect: %s", exc)
                    await interaction.followup.send("❌ Failed to connect to your voice channel.", ephemeral=True)
                    return
            elif player.channel != voice_channel:
                await interaction.followup.send(
                    f"❌ I'm already in {player.channel.mention}. Join that channel or stop playback first.",
                    ephemeral=True,
                )
                return
            player._text_channel = interaction.channel  # type: ignore[attr-defined]
            player._playlist_ctx = None  # type: ignore[attr-defined]
            try:
                results: wavelink.Search = await self._safe_search(query)
            except Exception as exc:
                logger.error("Search error: %s", exc)
                if we_connected:
                    await self._safe_disconnect_player(player, reason="play search error")
                await interaction.followup.send("❌ Could not reach the music server. Try again in a moment.", ephemeral=True)
                return
            if not results:
                if we_connected:
                    await self._safe_disconnect_player(player, reason="play no results")
                await interaction.followup.send("❌ No results found for that query.", ephemeral=True)
                return
            already_playing = player.playing or player.paused
            if isinstance(results, wavelink.Playlist):
                added = await player.queue.put_wait(results)
                confirm_text = f"✅ Added playlist **{results.name}** ({added} tracks) to the queue."
            else:
                track: wavelink.Playable = results[0]
                await player.queue.put_wait(track)
                confirm_text = f"✅ Added **{track.title}** by *{track.author}* to the queue."
            if not player.current:
                next_track = player.queue.get()
                player.last_track = next_track  # type: ignore[attr-defined]
                try:
                    await player.play(next_track)
                    await asyncio.sleep(CONTROL_FOLLOWUP_GRACE_SECONDS)
                    if not getattr(player, "_control_msg", None):
                        await self._send_control_followup(player, MusicControlView(self, player), interaction)
                except Exception as e:
                    logger.error("[PLAY] player.play() failed: %s - attempting node failover", e)
                    _fallback_channel = player.channel or voice_channel
                    await self._safe_disconnect_player(player, reason="play initial failover")
                    await asyncio.sleep(1)
                    try:
                        player = await self._safe_connect(interaction.guild, _fallback_channel)
                        player._text_channel = interaction.channel  # type: ignore[attr-defined]
                        player._playlist_ctx = None  # type: ignore[attr-defined]
                        self._guild_players[interaction.guild.id] = player
                        await player.play(next_track)
                        await asyncio.sleep(CONTROL_FOLLOWUP_GRACE_SECONDS)
                        if not getattr(player, "_control_msg", None):
                            await self._send_control_followup(player, MusicControlView(self, player), interaction)
                    except Exception as e2:
                        logger.error("[PLAY] Node failover also failed: %s", e2)
                        await interaction.followup.send("❌ I couldn't start the track. Please try again.", ephemeral=True)
                        return
            elif already_playing:
                control_sent = await self._update_control_msg(player, MusicControlView(self, player))
                if not control_sent:
                    await self._send_control_followup(player, MusicControlView(self, player), interaction)
            await interaction.followup.send(confirm_text)
        finally:
            self._processing_interactions.discard(interaction.id)

    @app_commands.command(name="queue", description="See the upcoming tracks in the queue")
    async def queue(self, interaction: discord.Interaction) -> None:
        await safe_defer(interaction)
        player: wavelink.Player = interaction.guild.voice_client  # type: ignore[assignment]
        if player is None or player.queue.count == 0:
            await send_interaction_message(interaction, "📭 The queue is empty right now. Add a song with /play.", ephemeral=True)
            return
        lines: list[str] = []
        for i, track in enumerate(player.queue, start=1):
            lines.append(f"`{i}.` **{track.title}** - *{track.author}* `[{format_duration(track.length)}]`")
            if i >= 20:
                remaining = player.queue.count - 20
                if remaining:
                    lines.append(f"*… and {remaining} more track(s)*")
                break
        current = player.current
        now = (f"**Now playing:** {current.title} - *{current.author}*\n\n" if current else "")
        embed = discord.Embed(
            title="🎵 Current Queue",
            description=now + "\n".join(lines),
            colour=discord.Colour.blurple(),
        )
        embed.set_footer(text=f"{player.queue.count} track(s) in queue")
        await send_interaction_message(interaction, embed=embed, ephemeral=True)

    @app_commands.command(name="skip", description="Skip the current song and play the next one in the queue")
    async def skip(self, interaction: discord.Interaction) -> None:
        await safe_defer(interaction)
        if not interaction.user.voice or not interaction.user.voice.channel:  # type: ignore[union-attr]
            await send_interaction_message(interaction, "❌ You need to jump into a voice channel first!", ephemeral=True)
            return
        player: wavelink.Player = interaction.guild.voice_client  # type: ignore[assignment]
        if player is None or not player.current:
            await send_interaction_message(interaction, "❌ Nothing is playing right now. Toss some music in!", ephemeral=True)
            return
        if interaction.user.voice.channel != player.channel:  # type: ignore[union-attr]
            await send_interaction_message(interaction, "❌ You need to be in the same voice channel as me to do that!", ephemeral=True)
            return
        skipped = player.current
        async with getattr(player, "queue_lock", asyncio.Lock()):
            if player.queue.is_empty:
                player._intentional_disconnect = True  # type: ignore[attr-defined]
                self._guild_players.pop(player.guild.id, None)
                await player.stop()
                await self._safe_disconnect_player(player, reason="skip empty queue")
                await send_interaction_message(interaction, f"⏭️ Skipped **{skipped.title}** - queue is now empty.", ephemeral=True)
                return
            next_track = player.queue.get()
            player.last_track = next_track  # type: ignore[attr-defined]
            await player.play(next_track)
        await send_interaction_message(interaction, f"⏭️ Skipped **{skipped.title}** by *{skipped.author}*.", ephemeral=True)

    @app_commands.command(name="stop", description="Stop playback, wipe the entire queue, and disconnect the bot")
    async def stop(self, interaction: discord.Interaction) -> None:
        await safe_defer(interaction)
        if not interaction.user.voice or not interaction.user.voice.channel:  # type: ignore[union-attr]
            await send_interaction_message(interaction, "❌ You need to jump into a voice channel first!", ephemeral=True)
            return
        player: wavelink.Player = interaction.guild.voice_client  # type: ignore[assignment]
        if player is None:
            await send_interaction_message(interaction, "❌ The bot is not connected.", ephemeral=True)
            return
        if interaction.user.voice.channel != player.channel:  # type: ignore[union-attr]
            await send_interaction_message(interaction, "❌ You need to be in the same voice channel as me to do that!", ephemeral=True)
            return
        player.queue.clear()
        player._intentional_disconnect = True  # type: ignore[attr-defined]
        self._guild_players.pop(player.guild.id, None)
        await player.stop()
        await self._safe_disconnect_player(player, reason="stop command")
        await send_interaction_message(interaction, "⏹️ Stopped playback, cleared the queue, and left the channel.")

    @app_commands.command(name="nowplaying", description="Show the current song, progress bar, and playback info")
    async def nowplaying(self, interaction: discord.Interaction) -> None:
        await safe_defer(interaction)
        player: wavelink.Player = interaction.guild.voice_client  # type: ignore[assignment]
        if player is None or not player.current:
            await send_interaction_message(interaction, "❌ Nothing is playing right now. Toss some music in!", ephemeral=True)
            return
        track = player.current
        pos = player.position
        dur = track.length
        bar = make_progress_bar(pos, dur)
        loop_mode = getattr(player.queue, "mode", None)
        if loop_mode == wavelink.QueueMode.loop:
            loop_label = "🔂 Track"
        elif loop_mode == wavelink.QueueMode.loop_all:
            loop_label = "🔁 Queue"
        else:
            loop_label = "➡️ Off"
        embed = discord.Embed(
            title="🎵 Now Playing",
            description=(
                f"**{track.title}**\n*by {track.author}*\n\n"
                f"`{format_duration(pos)}` {bar} `{format_duration(dur)}`"
            ),
            colour=discord.Colour.blurple(),
        )
        embed.add_field(name="Volume", value=f"🔊 {player.volume}%", inline=True)
        embed.add_field(name="Loop", value=loop_label, inline=True)
        embed.add_field(name="Queue", value=f"{player.queue.count} track(s)", inline=True)
        if track.artwork:
            embed.set_thumbnail(url=track.artwork)
        await send_interaction_message(interaction, embed=embed, ephemeral=True)

    @app_commands.command(name="shuffle", description="Shuffle the queued songs while keeping the current song playing")
    async def shuffle(self, interaction: discord.Interaction) -> None:
        if interaction.id in self._processing_interactions:
            await interaction.response.send_message("⏳ Already shuffling...", ephemeral=True)
            return
        self._processing_interactions.add(interaction.id)
        try:
            await safe_defer(interaction)
            if not interaction.user.voice or not interaction.user.voice.channel:  # type: ignore[union-attr]
                await send_interaction_message(interaction, "❌ You need to jump into a voice channel first!", ephemeral=True)
                return
            player: wavelink.Player = interaction.guild.voice_client  # type: ignore[assignment]
            if player is None or not player.current:
                await send_interaction_message(interaction, "❌ Nothing is playing right now. Toss some music in!", ephemeral=True)
                return
            if interaction.user.voice.channel != player.channel:  # type: ignore[union-attr]
                await send_interaction_message(interaction, "❌ You need to be in the same voice channel as me to do that!", ephemeral=True)
                return
            if player.queue.count == 0:
                await send_interaction_message(interaction, "❌ The queue is empty, so there's nothing to shuffle.", ephemeral=True)
                return
            async with getattr(player, "queue_lock", asyncio.Lock()):
                player.queue.shuffle()
            await send_interaction_message(interaction, f"🔀 Shuffled **{player.queue.count}** tracks in the queue.", ephemeral=True)
        finally:
            self._processing_interactions.discard(interaction.id)

    @app_commands.command(name="loop", description="Set loop mode: track, queue, or off")
    @app_commands.describe(mode="Choose what to loop: the current track, the whole queue, or turn looping off")
    @app_commands.choices(mode=[
        app_commands.Choice(name="🔂 Track - repeat the current song forever", value="track"),
        app_commands.Choice(name="🔁 Queue - loop through all songs in order", value="queue"),
        app_commands.Choice(name="➡️ Off - play through the queue once and stop", value="off"),
    ])
    async def loop(self, interaction: discord.Interaction, mode: str) -> None:
        await safe_defer(interaction)
        if not interaction.user.voice or not interaction.user.voice.channel:  # type: ignore[union-attr]
            await send_interaction_message(interaction, "❌ You need to jump into a voice channel first!", ephemeral=True)
            return
        player: wavelink.Player = interaction.guild.voice_client  # type: ignore[assignment]
        if player is None:
            await send_interaction_message(interaction, "❌ The bot is not connected.", ephemeral=True)
            return
        if interaction.user.voice.channel != player.channel:  # type: ignore[union-attr]
            await send_interaction_message(interaction, "❌ You need to be in the same voice channel as me to do that!", ephemeral=True)
            return
        if mode == "track":
            player.queue.mode = wavelink.QueueMode.loop
            await send_interaction_message(interaction, "🔂 **Loop:** Repeating the current track.", ephemeral=True)
        elif mode == "queue":
            player.queue.mode = wavelink.QueueMode.loop_all
            await send_interaction_message(interaction, "🔁 **Loop:** Looping the entire queue.", ephemeral=True)
        else:
            player.queue.mode = wavelink.QueueMode.normal
            await send_interaction_message(interaction, "➡️ **Loop:** Off - playing through once.", ephemeral=True)

    @app_commands.command(name="volume", description="Set the playback volume (0–200)")
    @app_commands.describe(level="Volume level from 0 (muted) to 200 (max boost) - 100 is the default")
    async def volume(self, interaction: discord.Interaction, level: int) -> None:
        await safe_defer(interaction)
        if not interaction.user.voice or not interaction.user.voice.channel:  # type: ignore[union-attr]
            await send_interaction_message(interaction, "❌ You need to jump into a voice channel first!", ephemeral=True)
            return
        player: wavelink.Player = interaction.guild.voice_client  # type: ignore[assignment]
        if player is None:
            await send_interaction_message(interaction, "❌ The bot is not connected.", ephemeral=True)
            return
        if interaction.user.voice.channel != player.channel:  # type: ignore[union-attr]
            await send_interaction_message(interaction, "❌ You need to be in the same voice channel as me to do that!", ephemeral=True)
            return
        if not 0 <= level <= 200:
            await send_interaction_message(interaction, "❌ Volume must be between **0** and **200**.", ephemeral=True)
            return
        await player.set_volume(level)
        emoji = "🔇" if level == 0 else "🔉" if level < 50 else "🔊"
        await send_interaction_message(interaction, f"{emoji} Volume set to **{level}%**.", ephemeral=True)

    @app_commands.command(name="remove", description="Remove a specific song from the queue by its number")
    @app_commands.describe(index="The position number of the song you want to remove (get the number from /queue)")
    async def remove(self, interaction: discord.Interaction, index: int) -> None:
        await safe_defer(interaction)
        if not interaction.user.voice or not interaction.user.voice.channel:  # type: ignore[union-attr]
            await send_interaction_message(interaction, "❌ You need to jump into a voice channel first!", ephemeral=True)
            return
        player: wavelink.Player = interaction.guild.voice_client  # type: ignore[assignment]
        if player is None or player.queue.count == 0:
            await send_interaction_message(interaction, "❌ The queue is completely empty!", ephemeral=True)
            return
        if interaction.user.voice.channel != player.channel:  # type: ignore[union-attr]
            await send_interaction_message(interaction, "❌ You need to be in the same voice channel as me to do that!", ephemeral=True)
            return
        if not 1 <= index <= player.queue.count:
            await send_interaction_message(interaction,
                f"❌ That number is out of range. Pick a value from **1** to **{player.queue.count}**.", ephemeral=True)
            return
        async with getattr(player, "queue_lock", asyncio.Lock()):
            tracks = list(player.queue)
            removed = tracks[index - 1]
            player.queue.clear()
            for t in tracks:
                if t is removed:
                    continue
                player.queue.put(t)  # type: ignore[arg-type]
        await send_interaction_message(interaction,
            f"❌ Removed **{removed.title}** by *{removed.author}* from position **{index}**.", ephemeral=True)

    @app_commands.command(name="autoplay", description="Toggle autoplay: when your queue runs out, the bot finds and plays a related song")
    async def autoplay(self, interaction: discord.Interaction) -> None:
        await safe_defer(interaction)
        gid = interaction.guild_id  # type: ignore[arg-type]
        current = self._autoplay.get(gid, False)
        self._autoplay[gid] = not current
        state = "✅ **On**" if not current else "❌ **Off**"
        hint = " - I'll find related songs when your queue ends." if not current else " - Music will stop when the queue runs out."
        await send_interaction_message(interaction, f"🎶 Autoplay: {state}{hint}", ephemeral=True)

    @app_commands.command(name="lyrics", description="📝 Show lyrics for the current track")
    async def lyrics(self, interaction: discord.Interaction) -> None:
        player: wavelink.Player = interaction.guild.voice_client  # type: ignore[assignment]
        if player is None or not player.current:
            await send_interaction_message(interaction, "❌ Nothing is playing right now. Toss some music in!", ephemeral=True)
            return
        track = player.current
        title = (track.title or "").strip()
        artist = (track.author or "").strip()
        await interaction.response.defer()
        params = {"track_name": title}
        if artist and artist.lower() != "unknown":
            params["artist_name"] = artist
        try:
            async with aiohttp.ClientSession() as session:
                async with session.get(
                    "https://lrclib.net/api/get",
                    params=params,
                    timeout=aiohttp.ClientTimeout(total=LYRICS_API_TIMEOUT_SECONDS),
                ) as resp:
                    if resp.status != 200:
                        await interaction.followup.send(f"❌ Lyrics not found for **{title}**.")
                        return
                    data = await resp.json()
            lyrics = (data.get("plainLyrics") or "").strip()
            if not lyrics:
                await interaction.followup.send(f"❌ No static full lyrics available for **{title}**.")
                return
            content = f"📝 **Lyrics: {title}**\n"
            if artist and artist.lower() != "unknown":
                content += f"👤 **Artist:** {artist}\n"
            content += "\n" + lyrics
            remaining = content
            while remaining:
                if len(remaining) <= MESSAGE_CHUNK_SIZE:
                    await interaction.followup.send(remaining)
                    break
                split_at = remaining.rfind("\n", 0, MESSAGE_CHUNK_SIZE)
                if split_at < 0:
                    split_at = MESSAGE_CHUNK_SIZE
                await interaction.followup.send(remaining[:split_at])
                remaining = remaining[split_at:].lstrip("\n")
        except Exception as exc:
            logger.warning("[LYRICS] Error: %s", exc)
            await interaction.followup.send("❌ Failed to fetch lyrics right now.")

    @app_commands.command(name="bitrate", description="📶 Show the current music bitrate tier")
    async def bitrate(self, interaction: discord.Interaction) -> None:
        await safe_defer(interaction)
        tier = await get_tier_from_message(interaction)
        voice_channel = interaction.user.voice.channel if interaction.user.voice else None  # type: ignore[union-attr]
        kbps = _get_target_bitrate(tier, voice_channel)
        channel_bitrate = (
            f"{voice_channel.bitrate // 1000}kbps"
            if voice_channel and getattr(voice_channel, "bitrate", None)
            else "N/A"
        )
        await send_interaction_message(interaction,
            f"📶 Music bitrate: **{kbps}kbps** (tier: **{tier}**, channel cap: **{channel_bitrate}**).",
            ephemeral=True,
        )

    @app_commands.command(name="bassboost", description="🔊 Apply bass boost filter")
    async def bassboost(self, interaction: discord.Interaction) -> None:
        await safe_defer(interaction)
        await self._run_filter_command(interaction, preset="bassboost", name="Bass Boost", emoji="🔊")

    @app_commands.command(name="nightcore", description="🎤 Apply nightcore filter")
    async def nightcore(self, interaction: discord.Interaction) -> None:
        await safe_defer(interaction)
        await self._run_filter_command(interaction, preset="nightcore", name="Nightcore", emoji="🎤")

    @app_commands.command(name="slow", description="🐌 Apply slowed filter")
    async def slow(self, interaction: discord.Interaction) -> None:
        await safe_defer(interaction)
        await self._run_filter_command(interaction, preset="slow", name="Slowed", emoji="🐌")

    @app_commands.command(name="eightd", description="🎧 Apply 8D filter")
    async def eightd(self, interaction: discord.Interaction) -> None:
        await safe_defer(interaction)
        await self._run_filter_command(interaction, preset="8d", name="8D", emoji="🎧")

    @app_commands.command(name="treble", description="🎚️ Apply treble boost filter")
    async def treble(self, interaction: discord.Interaction) -> None:
        await safe_defer(interaction)
        await self._run_filter_command(interaction, preset="treble", name="Treble", emoji="🎚️")

    @app_commands.command(name="lofi", description="📻 Apply lo-fi filter")
    async def lofi(self, interaction: discord.Interaction) -> None:
        await safe_defer(interaction)
        await self._run_filter_command(interaction, preset="lofi", name="Lo-fi", emoji="📻")

    @app_commands.command(name="vaporwave", description="🌫️ Apply vaporwave filter")
    async def vaporwave(self, interaction: discord.Interaction) -> None:
        await safe_defer(interaction)
        await self._run_filter_command(interaction, preset="vaporwave", name="Vaporwave", emoji="🌫️")

    @app_commands.command(name="resetfilters", description="♻️ Reset all music filters")
    async def resetfilters(self, interaction: discord.Interaction) -> None:
        await safe_defer(interaction)
        await self._run_filter_command(interaction, preset="reset", name="Reset", emoji="♻️")

    @app_commands.command(name="playlistcreate", description="🎵 Create a new server playlist from song URLs or queries")
    async def playlistcreate(self, interaction: discord.Interaction):
        if interaction.guild is None:
            await send_interaction_message(interaction, "❌ You can only use this command inside a server!", ephemeral=True)
            return
        await interaction.response.send_modal(PlaylistCreateModal(self))

    @app_commands.command(name="playlist", description="🎵 Browse, play, and manage server playlists")
    async def playlist(self, interaction: discord.Interaction):
        await safe_defer(interaction)
        if interaction.guild is None:
            await send_interaction_message(interaction, "❌ You can only use this command inside a server!", ephemeral=True)
            return
        playlists = playlist_manager.get_guild_playlists(interaction.guild.id)
        if not playlists:
            embed = discord.Embed(
                title="🎵 Server Playlists",
                description="No playlists saved yet.\n\nUse `/playlistcreate` to create your first playlist!",
                color=0x1DB954,
            )
            await send_interaction_message(interaction, embed=embed)
            return
        embed = self._build_playlist_browser_embed(interaction.guild.id, interaction.user.id)
        view = PlaylistBrowserView(self, interaction.guild.id, interaction.user.id)
        await send_interaction_message(interaction, embed=embed, view=view)

    @app_commands.command(name="history", description="See the last 10 songs played in this server")
    async def history(self, interaction: discord.Interaction) -> None:
        await safe_defer(interaction)
        gid = interaction.guild_id  # type: ignore[arg-type]
        hist = self._history.get(gid, [])
        if not hist:
            await send_interaction_message(interaction, "📭 No playback history yet for this server.", ephemeral=True)
            return
        lines = [
            f"`{i}.` **{title}** - *{author}* `[{format_duration(dur)}]`"
            for i, (title, author, dur) in enumerate(reversed(hist), start=1)
        ]
        embed = discord.Embed(
            title="📜 Recently Played",
            description="\n".join(lines),
            colour=discord.Colour.blurple(),
        )
        embed.set_footer(text="Showing the last 10 tracks played in this server")
        await send_interaction_message(interaction, embed=embed, ephemeral=True)

    @commands.Cog.listener()
    async def on_wavelink_websocket_closed(self, payload: wavelink.WebsocketClosedEventPayload) -> None:
        player: wavelink.Player = payload.player
        if not player:
            return
        await asyncio.sleep(5.0)
        if player.guild.id in self._recovering_guilds:
            return
        if getattr(player, "_recovering", False):
            return
        if getattr(player, "_intentional_disconnect", False):
            return
        if player.playing or player.paused or player.connected:
            return
        await self._guild_recovery_controller(
            player,
            reason="websocket closed recovery",
            exclude={getattr(player.node, "identifier", "")}
        )


    @commands.Cog.listener()
    async def on_wavelink_node_closed(self, node: wavelink.Node, _code: int, _reason: str) -> None:
        logger.error("[NODE] Node %s died (code: %s, reason: %s)", node.identifier, _code, _reason)

    @commands.Cog.listener()
    async def on_voice_state_update(
        self, member: discord.Member,
        before: discord.VoiceState, after: discord.VoiceState,
    ) -> None:
        if member.id != self.bot.user.id:
            return
        if before.channel is None or after.channel is not None:
            return
        gid = member.guild.id
        player = self._guild_players.get(gid)
        if player is None:
            return
        if getattr(player, "_intentional_disconnect", False) or gid in self._recovering_guilds:
            return
        now = time.time()
        last_vc = float(getattr(player, "_last_voice_disconnect_at", 0.0) or 0.0)
        if now - last_vc < 5:
            return
        player._last_voice_disconnect_at = now  # type: ignore[attr-defined]
        if getattr(player, "_recovering", False) or float(getattr(player, "_suppress_failover_until", 0) or 0) > time.time():
            logger.debug("[VOICE] Ignoring temporary VC leave for guild %s during recovery/source handling.", gid)
            return
        original_player = player
        await asyncio.sleep(15)
        current_player = self._guild_players.get(gid)
        if current_player is not original_player:
            logger.debug("[VOICE] Player changed during disconnect wait for guild %s; aborting stale cleanup.", gid)
            return
        if current_player is None or current_player.connected or gid in self._recovering_guilds:
            return
        if getattr(current_player, "_recovering", False):
            return
        if getattr(current_player, "_intentional_disconnect", False):
            return
        if current_player.playing or current_player.paused:
            return
        last_track_start = float(getattr(current_player, "_last_track_start", 0.0) or 0.0)
        if last_track_start and (time.monotonic() - last_track_start < 15):
            logger.debug("[VOICE] Skipping cleanup for guild %s due to very recent track start.", gid)
            return
        last_disconnect_at = float(getattr(current_player, "_last_voice_disconnect_at", 0.0) or 0.0)
        if not last_disconnect_at or (time.time() - last_disconnect_at < 15):
            logger.debug("[VOICE] Disconnect for guild %s has not been sustained long enough; skipping cleanup.", gid)
            return
        should_attempt_recovery = bool(current_player.current) or (not current_player.queue.is_empty)
        if should_attempt_recovery:
            logger.warning("[VOICE] Unexpected VC disconnect in guild %s; attempting recovery before cleanup.", gid)
            recovered = await self._guild_recovery_controller(
                current_player,
                reason="voice state disconnect recovery",
                exclude={getattr(current_player.node, "identifier", "")},
            )
            if recovered is not None and (recovered.connected or recovered.playing or recovered.paused):
                logger.info("[VOICE] Recovery succeeded for guild %s after voice disconnect.", gid)
                return
        logger.warning("[VOICE] Bot unexpectedly disconnected from VC '%s' in guild %s - cleaning up.", before.channel.name, gid)
        self._guild_players.pop(gid, None)
        
        control_msg: discord.Message | None = getattr(current_player, "_control_msg", None)
        if control_msg:
            stopped_view = discord.ui.LayoutView(timeout=None)
            stopped_view.add_item(discord.ui.Container(
                discord.ui.TextDisplay("### ⏹️  Playback stopped\n-# The bot was disconnected from the voice channel."),
                accent_colour=discord.Colour.red(),
            ))
            try:
                await control_msg.edit(content=None, embed=None, view=stopped_view)
            except Exception:
                pass

        await self._safe_disconnect_player(current_player, reason="unexpected voice disconnect cleanup")

    @commands.Cog.listener()
    async def on_wavelink_track_end(self, payload: wavelink.TrackEndEventPayload) -> None:
        player: wavelink.Player = payload.player
        if not player:
            logger.warning("[TRACK END] payload.player is None for '%s' - node destroyed player, attempting recovery.",
                getattr(payload.track, "title", "?"))
            _vc_id = getattr(payload, "voice_channel_id", None)
            found_gid = None
            for gid, stored in self._guild_players.items():
                if (stored.channel and _vc_id and stored.channel.id == _vc_id) or (getattr(stored, 'last_track', None) == payload.track):
                    player = stored
                    found_gid = gid
                    logger.warning("[TRACK END] Recovered player for guild %s via channel/track match", gid)
                    break
            
            if not player:
                logger.error("[TRACK END] Could not recover player info for recovery - giving up.")
                return
            
            logger.warning("[TRACK END] Performing HARD RECOVERY for guild %s", player.guild.id)
            switched = await self._switch_player_to_healthy_node(
                player,
                reason="hard recovery (player is None)"
            )
            if switched:
                if not switched.queue.is_empty:
                    next_t = switched.queue.get()
                    switched.last_track = next_t
                    await switched.play(next_t)
                elif self._autoplay.get(player.guild.id, False):
                    pass
            return
        active_node = getattr(player, "_active_node_id", None)
        if active_node and player.node.identifier != active_node:
            logger.debug("[TRACK END] Ignoring stale node event from %s (active=%s).", player.node.identifier, active_node)
            return
        if getattr(player, "_recovering", False) or getattr(player, "_transitioning", False):
            logger.debug("[TRACK END] Ignoring event during recovery/transition for guild %s.", player.guild.id)
            return
        if not player.connected:
            logger.debug("[TRACK END] Ignoring disconnected player event for guild %s.", player.guild.id)
            return

        reason = str(payload.reason).lower()
        if reason in ("loadfailed", "load_failed", "stopped"):
            logger.warning("[TRACK END] reason=%s for '%s'", payload.reason, getattr(payload.track, "title", "?"))
        else:
            logger.debug("[TRACK END] reason=%s for '%s'", payload.reason, getattr(payload.track, "title", "?"))

        if getattr(player, '_intentional_disconnect', False):
            logger.debug("[TRACK END] Skipping - player already intentionally disconnected.")
            return

        stored_player = self._guild_players.get(player.guild.id)
        if stored_player and getattr(stored_player, '_intentional_disconnect', False):
            logger.debug("[TRACK END] Skipping - stored player intentionally disconnected.")
            return

        if reason != "finished":
            logger.debug("[TRACK END] Ignoring non-finished reason=%s.", payload.reason)
            return

        gid = player.guild.id
        suppress_advance_until = float(getattr(player, '_suppress_track_end_advance_until', 0) or 0)
        if suppress_advance_until > time.time() and reason in ("load_failed", "loadfailed", "replaced", "stopped"):
            logger.debug("[TRACK END] Suppressing duplicate queue advance for '%s' after track_exception already advanced.",
                getattr(payload.track, "title", "?"))
            player._recovering = False  # type: ignore[attr-defined]
            return

        source_suppress_until = float(getattr(player, '_suppress_failover_until', 0) or 0)

        if reason == "stopped" and not player.connected:
            if source_suppress_until > time.time():
                logger.debug("[TRACK END] Source-suppress active for guild %s; skip reconnect on stopped.", gid)
                player._recovering = False  # type: ignore[attr-defined]
                return
            player._suppress_failover_until = time.time() + NODE_STOPPED_SUPPRESS_SECONDS  # type: ignore[attr-defined]
            player._recovering = False  # type: ignore[attr-defined]
            logger.warning("[TRACK END] Node stopped/destroyed player for guild %s; attempting to resume interrupted track.", gid)
            
            track_to_resume = getattr(player, 'last_track', None) or payload.track
            if not track_to_resume:
                if player.queue.is_empty:
                    return
                track_to_resume = player.queue.get()
                
            player.last_track = track_to_resume  # type: ignore[attr-defined]
            switched_player = await self._switch_player_to_healthy_node(
                player,
                exclude={getattr(player.node, "identifier", "")},
                reason="node stopped, recovering track",
            )
            if switched_player is None:
                return
            try:
                await switched_player.play(track_to_resume)
            except Exception as exc:
                logger.error("[TRACK END] Failed to restart track after stopped event: %s", exc)
            return

        if not player.connected and player.channel:
            if self._guild_players.get(gid) is not player:
                logger.warning("[RECONNECT] Skipping stale player reconnect for guild %s - a newer player already exists.", gid)
                return
            should_continue_queue = (not player.queue.is_empty) or self._autoplay.get(gid, False)
            if source_suppress_until > time.time():
                if not should_continue_queue:
                    logger.warning("[RECONNECT] Not reconnecting guild %s after source-level load failure; no queued recovery work.", gid)
                else:
                    failed_node = getattr(player.node, "identifier", None)
                    logger.warning("[RECONNECT] Source-level failure disconnected guild %s with queued tracks; rebuilding on healthy node.", gid)
                    switched_player = await self._switch_player_to_healthy_node(
                        player,
                        exclude={failed_node} if failed_node else None,
                        reason="track_end source disconnect",
                    )
                    if switched_player is None:
                        return
                    player = switched_player
            else:
                try:
                    logger.warning("[RECONNECT] Player disconnected, reconnecting to %s", player.channel.id)
                    await player.connect(timeout=VC_CONNECT_TIMEOUT, self_deaf=True, reconnect=True)
                except Exception as e:
                    logger.error("[RECONNECT] Failed to reconnect: %s", e)
                    return

        if getattr(player, "_recovering", False) or player.guild.id in self._recovering_guilds:
            return

        async with getattr(player, "queue_lock", asyncio.Lock()):
            player._transitioning = True  # type: ignore[attr-defined]
            next_track = None
            try:
                if not player.queue.is_empty:
                    next_track = player.queue.get()
                    player.last_track = next_track  # type: ignore[attr-defined]
                if next_track:
                    try:
                        await player.play(next_track)
                        self._snapshot_playback(player)
                        return
                    except Exception as e:
                        logger.error("[QUEUE] Failed to play next track: %s", e)
            finally:
                player._transitioning = False  # type: ignore[attr-defined]

        if self._autoplay.get(gid, False):
            try:
                last_track = getattr(player, 'last_track', None) or payload.track
                if last_track:
                    ap_hist = self._autoplay_history.get(gid, [])
                    search_query = f"ytmsearch:{last_track.title} {last_track.author}"
                    if len(ap_hist) >= 5:
                        last_5_cores = [e['core'] for e in ap_hist[-5:]]
                        if len(set(last_5_cores)) <= 2:
                            escape_pool = [e['core'] for e in ap_hist[:-5] if e.get('core')]
                            pivot = random.choice(escape_pool) if escape_pool else random.choice(last_5_cores)
                            search_query = f"ytmsearch:{pivot} similar new song"
                            logger.warning("[AUTOPLAY] Loop detected - escaping with pivot='%s'", pivot)
                    logger.info("[AUTOPLAY] Finding related track for: %s", last_track.title)
                    related = await self._safe_search(search_query)
                    if related and len(related) > 1:
                        next_track = None
                        for candidate in related[1:8]:
                            words = _strong_words(candidate.title)
                            if not _is_duplicate(candidate, ap_hist, c_words=words):
                                next_track = candidate
                                break
                        if next_track is None:
                            next_track = related[1]
                        logger.info("[AUTOPLAY] Selected: '%s'", next_track.title)
                        player.last_track = next_track  # type: ignore[attr-defined]
                        await player.play(next_track)
                        return
            except Exception as e:
                logger.error("[AUTOPLAY] Failed to find related track: %s", e)


        logger.info("[IDLE CHECK] Queue empty for guild %s, waiting 2s", gid)
        await asyncio.sleep(2)
        if player.playing or not player.queue.is_empty:
            return
        if player.paused:
            return
        if getattr(player, '_recovering', False):
            return
        if getattr(player, '_intentional_disconnect', False):
            return
        last_track_start = float(getattr(player, "_last_track_start", 0.0) or 0.0)
        if last_track_start and (time.monotonic() - last_track_start < 15):
            logger.debug("[IDLE CHECK] Skipping idle disconnect for guild %s due to recent track start.", gid)
            return

        logger.info("[DISCONNECT] Confirmed idle for guild %s, disconnecting", gid)
        try:
            playlist_ctx = getattr(player, "_playlist_ctx", None)
            autoplay_on = self._autoplay.get(gid, False)
            if playlist_ctx and not autoplay_on:
                _end_text = (
                    f"### ✅  Playlist finished\n"
                    f"-# **{playlist_ctx['name']}** has ended.\n"
                    f"-# Queue finished  ·  The bot has left the VC."
                )
                _end_colour = discord.Colour.green()
            else:
                _end_text = "### ⏹️  Queue finished\n-# The bot has left the VC."
                _end_colour = discord.Colour.blurple()
            _end_view = discord.ui.LayoutView(timeout=None)
            _end_view.add_item(discord.ui.Container(
                discord.ui.TextDisplay(_end_text),
                accent_colour=_end_colour,
            ))
            await self._update_control_msg(player, _end_view)
            player._intentional_disconnect = True  # type: ignore[attr-defined]
            self._guild_players.pop(gid, None)
            self._autoplay_history.pop(gid, None)
            await self._safe_disconnect_player(player, reason="idle disconnect")
        except Exception:
            pass


async def setup(bot: commands.Bot) -> None:
    await bot.add_cog(Music(bot))
