# Maze-O Generator

A browser-based generator for **Maze-Orienteering (Maze-O)** courses and printable course materials.

**Try it online:** https://dknowles2.github.io/mazeo/

## What is Maze-O?

Maze-Orienteering is a compact, tabletop- or room-scale orienteering activity played on a **5×5 grid** with barriers (walls), a **Start** (`▲`) marker, and an **End** (`⊙`) marker. Each grid point holds a letter sign. Runners navigate from Start to End without crossing walls, visiting checkpoints in order and recording each letter to spell a secret word.

## Features

- **Custom Word Placement:** Enter up to **4 words** (up to **8 letters** each, A–Z). Shared letters are automatically reused across words to fit within the 25-cell grid, with non-crossing checkpoint ordering.
- **Interactive Preview:**
  - Click **Try Example** or press `Ctrl`/`⌘` + `Enter` to generate a maze immediately.
  - Select any word card to highlight its numbered steps on the grid and view step-by-step compass directions (`N`, `S`, `E`, `W`, `NE`, `SE`, `SW`, `NW`) that route around walls.
  - Toggle **Hide letters** to preview the blank dot-grid view used on runner sheets.
- **Printable Course Pack:** Opens a print-ready view with section checkboxes so you can print only what you need:
  - **Maze Coordinator (1 sheet):** Full 5×5 letter grid with walls, Start/End markers, compass rose, and word answer key.
  - **Maze Runner – Easy (1 per word):** Dot grid with numbered red control rings and letter boxes to fill in.
  - **Maze Runner – Hard (1 per word):** Blank dot grid with wall-aware compass directions, progress checkboxes, and letter boxes.
  - **Sign & Letter Cards (9 full sheets):** Large-print Start, End, and all 25 grid letters with orientation underlines, horizontal cut lines, and center fold lines to make standing signs.

## Running Locally

This is a zero-dependency static web app (`HTML`, `CSS`, and vanilla `JavaScript`).

1. Clone the repository:
   ```bash
   git clone https://github.com/dknowles2/mazeo.git
   cd mazeo
   ```
2. Open `index.html` directly in your browser, or serve it locally:
   ```bash
   python3 -m http.server 8000
   ```
   Then visit `http://localhost:8000`.

## Project Structure

- `index.html` — App markup and semantic layout
- `style.css` — Responsive styles, accessibility focus/contrast rules, and direct print styles
- `script.js` — Grid solver, wall-aware BFS compass pathfinding, live SVG rendering, and printable sheet generator

## License

Licensed under the [Apache License 2.0](LICENSE).
