from pathlib import Path

from pypdf import PdfReader


CHAPTERS_DIR = Path("chapters")
TEXTBOOK_DIR = Path("textbook")


def chapter_number(pdf_path: Path) -> str:
    return pdf_path.name.split("-", maxsplit=1)[0]


def extract_pdf_text(pdf_path: Path) -> str:
    reader = PdfReader(pdf_path)
    pages = []
    for page_number, page in enumerate(reader.pages, start=1):
        text = page.extract_text() or ""
        text = "\n".join(line.rstrip() for line in text.splitlines())
        pages.append(f"\n\n--- page {page_number} ---\n\n{text.strip()}\n")
    return "".join(pages).strip() + "\n"


def output_path(pdf_path: Path) -> Path:
    chapter = chapter_number(pdf_path)
    return TEXTBOOK_DIR / f"ch{chapter}" / f"ch{int(chapter)}_excerpt.txt"


def main() -> None:
    pdf_paths = sorted(CHAPTERS_DIR.glob("[0-9][0-9]-*.pdf"))
    if not pdf_paths:
        raise SystemExit("no chapter PDFs found under chapters/")

    for pdf_path in pdf_paths:
        out_path = output_path(pdf_path)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        text = extract_pdf_text(pdf_path)
        out_path.write_text(text, encoding="utf-8")
        print(f"wrote {out_path} ({len(text.splitlines())} lines)")


if __name__ == "__main__":
    main()
