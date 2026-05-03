from __future__ import annotations

import argparse
import asyncio
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path

import edge_tts
from pydub import AudioSegment, effects


ROOT = Path(__file__).resolve().parents[1]
VIDEO = ROOT / "animations/media/videos/fwl_structure/1080p15/FWLStructure.mp4"
VOICEOVER_DIR = ROOT / "animations/media/voiceover"
NARRATION_WAV = VOICEOVER_DIR / "FWLStructure_voiceover.wav"
OUTPUT_VIDEO = ROOT / "animations/media/videos/fwl_structure/1080p15/FWLStructure_voiceover.mp4"


@dataclass(frozen=True)
class Segment:
    start: float
    duration: float
    text: str


SEGMENTS = [
    Segment(
        0.0,
        5.7,
        "This is the formal spine of Frisch Waugh Lovell in Chapter three F W L: "
        "full beta two equals residualized beta.",
    ),
    Segment(
        5.7,
        7.0,
        "Start with the full regression on from columns X one and X two. "
        "The full normal equations split into separate X one and X two blocks.",
    ),
    Segment(
        12.7,
        9.0,
        "Next build M one, the annihilator for X one. It kills X one, and turns "
        "X two and y into the residualized data used by the auxiliary regression.",
    ),
    Segment(
        21.7,
        8.3,
        "The bridge lemma rewrites the auxiliary residual at the full beta two "
        "coefficient as M one applied to the full residual. That is the main "
        "algebraic move.",
    ),
    Segment(
        30.0,
        7.0,
        "Because the full beta two block satisfies those auxiliary normal equations, "
        "uniqueness of O L S identifies it with the F W L coefficient.",
    ),
    Segment(
        37.0,
        5.3,
        "The coefficient identity gives matching residuals; the full residual is "
        "already orthogonal to X one.",
    ),
    Segment(
        42.3,
        4.3,
        "Proof map: normal equations plus annihilator bridges feed the coefficient "
        "and residual identities.",
    ),
    Segment(
        46.6,
        4.0,
        "Lean packages F W L as reusable bridges, not one long calculation.",
    ),
]


async def synthesize_segment(segment: Segment, index: int, voice: str, rate: str) -> Path:
    path = VOICEOVER_DIR / f"segment_{index:02d}.mp3"
    communicate = edge_tts.Communicate(segment.text, voice=voice, rate=rate)
    await communicate.save(str(path))
    return path


def fit_to_duration(audio: AudioSegment, duration_s: float, tail_padding_ms: int = 180) -> AudioSegment:
    target_ms = int(duration_s * 1000)
    speech_target_ms = max(250, target_ms - tail_padding_ms)
    audio = effects.normalize(audio).fade_in(25).fade_out(80)

    if len(audio) > speech_target_ms:
        factor = len(audio) / speech_target_ms
        audio = speed_change(audio, factor)

    if len(audio) < target_ms:
        audio += AudioSegment.silent(duration=target_ms - len(audio))

    return audio[:target_ms]


def speed_change(audio: AudioSegment, factor: float) -> AudioSegment:
    factor = max(factor, 1.0)
    with tempfile.NamedTemporaryFile(suffix=".wav", dir=VOICEOVER_DIR, delete=False) as in_file:
        input_path = Path(in_file.name)
    output_path = input_path.with_name(f"{input_path.stem}_tempo.wav")

    try:
        audio.export(input_path, format="wav")
        subprocess.run(
            [
                "ffmpeg",
                "-y",
                "-loglevel",
                "error",
                "-i",
                str(input_path),
                "-filter:a",
                f"atempo={factor:.6f}",
                str(output_path),
            ],
            check=True,
        )
        return AudioSegment.from_file(output_path)
    finally:
        input_path.unlink(missing_ok=True)
        output_path.unlink(missing_ok=True)


async def build_voiceover(voice: str, rate: str) -> Path:
    VOICEOVER_DIR.mkdir(parents=True, exist_ok=True)
    paths = await asyncio.gather(
        *[synthesize_segment(segment, i, voice, rate) for i, segment in enumerate(SEGMENTS)]
    )

    timeline = AudioSegment.silent(duration=int((SEGMENTS[-1].start + SEGMENTS[-1].duration) * 1000))
    for segment, path in zip(SEGMENTS, paths, strict=True):
        raw = AudioSegment.from_file(path)
        fitted = fit_to_duration(raw, segment.duration)
        timeline = timeline.overlay(fitted, position=int(segment.start * 1000))

    timeline = effects.normalize(timeline).apply_gain(-2.0)
    timeline.export(NARRATION_WAV, format="wav")
    return NARRATION_WAV


def mux_audio(video: Path, audio: Path, output: Path) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(
        [
            "ffmpeg",
            "-y",
            "-i",
            str(video),
            "-i",
            str(audio),
            "-map",
            "0:v:0",
            "-map",
            "1:a:0",
            "-c:v",
            "copy",
            "-c:a",
            "aac",
            "-b:a",
            "96k",
            "-shortest",
            str(output),
        ],
        check=True,
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate and splice the FWL structure voiceover.")
    parser.add_argument("--voice", default="en-US-GuyNeural")
    parser.add_argument("--rate", default="+12%")
    parser.add_argument("--video", type=Path, default=VIDEO)
    parser.add_argument("--output", type=Path, default=OUTPUT_VIDEO)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if not args.video.exists():
        raise FileNotFoundError(
            f"Input video not found: {args.video}. Render FWLStructure before adding voiceover."
        )

    audio = asyncio.run(build_voiceover(args.voice, args.rate))
    mux_audio(args.video, audio, args.output)
    print(f"Wrote narrated video: {args.output}")


if __name__ == "__main__":
    main()
