from pathlib import Path
import sys

from pypdf import PdfReader


def extract_pdf_text(pdf_path: Path) -> str:
    reader = PdfReader(pdf_path)
    pages = []
    for page_number, page in enumerate(reader.pages, start=1):
        text = page.extract_text() or ""
        text = "\n".join(line.rstrip() for line in text.splitlines())
        pages.append(f"\n\n--- page {page_number} ---\n\n{text.strip()}\n")
    return "".join(pages).strip() + "\n"


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: python scripts/0_extract_pdf_text.py <input.pdf> <output.txt>")

    input_path = Path(sys.argv[1])
    output_path = Path(sys.argv[2])
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(extract_pdf_text(input_path), encoding="utf-8")


if __name__ == "__main__":
    main()
