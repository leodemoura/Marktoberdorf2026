import VersoSlides
import Lectures.Lecture1
import Lectures.Lecture2
import Lectures.Lecture3
import Lectures.Lecture4

open VersoSlides
open System (FilePath)

def eventName := "Marktoberdorf Summer School | August 2026"

/-- Copy the static assets (CSS, logos, images) into a deck's output directory. -/
def copyStatic (outputDir : FilePath) : IO Unit := do
  let cssContents ← IO.FS.readFile "static/custom.css"
  IO.FS.writeFile (outputDir / "custom.css") cssContents
  let logoBytes ← IO.FS.readBinFile "static/lean-logo.png"
  IO.FS.writeBinFile (outputDir / "lean-logo.png") logoBytes
  let logoLargeBytes ← IO.FS.readBinFile "static/lean-logo-large.png"
  IO.FS.writeBinFile (outputDir / "lean-logo-large.png") logoLargeBytes
  let imagesDir := outputDir / "images"
  IO.FS.createDirAll imagesDir
  for entry in ← FilePath.readDir "static/images" do
    let bytes ← IO.FS.readBinFile entry.path
    IO.FS.writeBinFile (imagesDir / entry.fileName) bytes

/--
Post-process the generated `index.html`:
- inject the custom stylesheet and disable reveal.js layout,
- add the logo header to content slides,
- replace the title and thank-you slides with the styled versions.
-/
def postProcessHtml (outputDir : FilePath) (title lecture : String) : IO Unit := do
  let htmlPath := outputDir / "index.html"
  let html ← IO.FS.readFile htmlPath
  let html := html.replace "</head>" "<link rel=\"stylesheet\" href=\"custom.css\">\n    </head>"
  let html := html.replace "Reveal.initialize({" "Reveal.initialize({\n        disableLayout: true,"
  let slideHeader := "<div class=\"slide-header\"><img src=\"lean-logo.png\" alt=\"Lean\"></div>"
  let html := html.replace "<section>\n" s!"<section>\n          {slideHeader}\n"
  let html := html.replace "<section data-transition=\"fade\">\n" s!"<section data-transition=\"fade\">\n          {slideHeader}\n"
  -- Title slide
  let titleSlideOld := s!"<section data-background-color=\"#0073A3\">\n          <h2>\n            {title}</h2>\n          <p>\n            {lecture}</p>\n          <p>\n            Leonardo de Moura</p>\n          <p>\n            AWS | Lean FRO</p>\n          </section>"
  let titleSlideNew := s!"<section class=\"title-slide\">\n          <div class=\"top-area\"><img class=\"logo\" src=\"lean-logo-large.png\" alt=\"Lean Logo\"></div>\n          <div class=\"blue-band\"><h1>{title}</h1>\n          <div class=\"meta\"><strong>{lecture}</strong><br><strong>Leo de Moura</strong><br>Senior Principal Applied Scientist, AWS<br>Chief Architect, Lean FRO</div>\n          <div class=\"date\">{eventName}</div>\n          </div></section>"
  let html := html.replace titleSlideOld titleSlideNew
  -- Thank You slide
  let thankSlideOld := "<section data-background-color=\"#0073A3\">\n          <h2>\n            Thank You</h2>\n          <p>\n            <em>Leo de Moura</em></p>\n          <p>\n            lean-lang.org | leanprover.zulipchat.com\n</p>\n          </section>"
  let thankSlideNew := s!"<section class=\"title-slide\">\n          <div class=\"top-area\"><img class=\"logo\" src=\"lean-logo-large.png\" alt=\"Lean Logo\"></div>\n          <div class=\"blue-band\"><h1>Thank You</h1>\n          <div class=\"meta\"><strong>Leo de Moura</strong><br><a href=\"https://lean-lang.org\" style=\"color:#93c5fd;\">lean-lang.org</a><br><a href=\"https://leanprover.zulipchat.com/\" style=\"color:#93c5fd;\">leanprover.zulipchat.com</a><br><br><a href=\"https://leodemoura.github.io/\" style=\"color:#93c5fd;\">leodemoura.github.io</a></div>\n          <div class=\"date\">{eventName}</div>\n          </div></section>"
  let html := html.replace thankSlideOld thankSlideNew
  let pipelineOld := "Pipeline: Lean Goal → Preprocessing → Internalization → E-graph ⇔ cutsat ⇔ rings ⇔ linarith"
  let pipelineNew :=
    "</p><div class=\"pipeline\">" ++
    "<div class=\"step\">Lean Goal</div><span class=\"arrow\">→</span>" ++
    "<div class=\"step\">Preprocessing</div><span class=\"arrow\">→</span>" ++
    "<div class=\"step\">Internalization</div><span class=\"arrow\">→</span>" ++
    "<div class=\"step highlight\">E-graph</div><span class=\"arrow\">↔</span>" ++
    "<div class=\"step\">cutsat</div><span class=\"arrow\">↔</span>" ++
    "<div class=\"step\">rings</div><span class=\"arrow\">↔</span>" ++
    "<div class=\"step\">linarith</div><span class=\"arrow\">↔</span>" ++
    "<div class=\"step\">orders</div><span class=\"arrow\">↔</span>" ++
    "<div class=\"step\">ac</div>" ++
    "</div><p>"
  let html := html.replace pipelineOld pipelineNew
  -- Remove stray "---" paragraphs from hstack
  let html := html.replace "<p>\n              ---</p>" ""
  IO.FS.writeFile htmlPath html
  -- Inline hover data to avoid fetch CORS issues when opening as local files
  let docsJsonPath := outputDir / "-verso-docs.json"
  if ← docsJsonPath.pathExists then
    let docsJson ← IO.FS.readFile docsJsonPath
    let hlJsPath := outputDir / "lib" / "highlighting.js"
    if ← hlJsPath.pathExists then
      let hlJs ← IO.FS.readFile hlJsPath
      let hlJs := hlJs.replace
        "fetch(docsJson).then((resp) => resp.json()).then((versoDocData) => {"
        s!"Promise.resolve({docsJson}).then((versoDocData) => \{"
      let hlJs := hlJs.replace
        "window.onload = () => {"
        "window.addEventListener('load', () => {"
      IO.FS.writeFile hlJsPath hlJs
    let panelJsPath := outputDir / "lib" / "panel.js"
    if ← panelJsPath.pathExists then
      let panelJs ← IO.FS.readFile panelJsPath
      let panelJs := panelJs.replace
        "fetch(\"-verso-docs.json\")\n            .then(function (r) {\n                return r.ok ? r.json() : {};\n            })\n            .then(function (j) {\n                docsJson = j;\n            })\n            .catch(function () {\n                docsJson = {};\n            });"
        s!"docsJson = {docsJson};"
      IO.FS.writeFile panelJsPath panelJs

def buildDeck (doc : Verso.Doc.Part Slides) (dir : FilePath) (title lecture : String) :
    IO UInt32 := do
  let config : Config := {
    center := false, margin := 0, outputDir := dir,
    theme := "white", slideNumber := true, transition := "fade"
  }
  let rc ← slidesMain (config := config) (doc := doc)
  if rc != 0 then
    return rc
  copyStatic dir
  postProcessHtml dir title lecture
  return 0

/-- Hub page linking the four lecture decks. -/
def hubPage : String := "<!DOCTYPE html>
<html>
<head>
<meta charset=\"utf-8\">
<title>Lean 4 for Program Verification in the Age of AI</title>
<style>
body { font-family: -apple-system, 'Segoe UI', sans-serif; max-width: 40rem; margin: 4rem auto; padding: 0 1rem; color: #1a1a1a; }
h1 { font-size: 1.6rem; }
li { margin: 0.6rem 0; font-size: 1.1rem; }
a { color: #0073A3; }
</style>
</head>
<body>
<h1>Lean 4 for Program Verification in the Age of AI</h1>
<p>Leonardo de Moura — Marktoberdorf Summer School, Herrsching am Ammersee, August 2026</p>
<ol>
<li><a href=\"lecture1/index.html\">Introduction to Lean and Dependent Type Theory</a></li>
<li><a href=\"lecture2/index.html\">Programming and Proving in Lean</a></li>
<li><a href=\"lecture3/index.html\">Proof Automation and AI</a></li>
<li><a href=\"lecture4/index.html\">Software Verification in Lean</a></li>
</ol>
</body>
</html>
"

/--
With no arguments, renders all four decks. With arguments (e.g.
`lake exe marktoberdorf2026 1 3`), renders only the named lectures.
-/
def main (args : List String) : IO UInt32 := do
  let want (n : String) : Bool := args.isEmpty || args.contains n
  let mut failed := false
  if want "1" then
    failed := failed || (← buildDeck (%doc Lectures.Lecture1) "_slides/lecture1"
      "Introduction to Lean and Dependent Type Theory" "Lecture 1 of 4") != 0
  if want "2" then
    failed := failed || (← buildDeck (%doc Lectures.Lecture2) "_slides/lecture2"
      "Programming and Proving in Lean" "Lecture 2 of 4") != 0
  if want "3" then
    failed := failed || (← buildDeck (%doc Lectures.Lecture3) "_slides/lecture3"
      "Proof Automation and AI" "Lecture 3 of 4") != 0
  if want "4" then
    failed := failed || (← buildDeck (%doc Lectures.Lecture4) "_slides/lecture4"
      "Software Verification in Lean" "Lecture 4 of 4") != 0
  if failed then
    IO.eprintln "Slide generation failed"
    return 1
  IO.FS.writeFile ("_slides" / "index.html" : FilePath) hubPage
  return 0
