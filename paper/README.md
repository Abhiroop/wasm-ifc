# paper/

The OOPSLA 2027 R1 submission (deadline 14 Oct 2026 AoE). `current/` is the Overleaf project as a
git submodule (`git submodule update --init paper/current`); pushing to Overleaf is a push of
that submodule, and is the maintainer's call.

## Building locally

```sh
cd paper/current && latexmk          # .latexmkrc: pdflatex -shell-escape (minted), BibTeX
```

Needs a TeX Live with `acmart`, `minted` (and `pygmentize`), `tikz`, `cleveref`. The
bibliography goes through BibTeX with `ACM-Reference-Format`, not biblatex, because the local
TeX Live lacks acmart's biblatex styles; Overleaf handles either.

## Layout

| Path | Contents |
|---|---|
| `current/main.tex` | acmart, `review, anonymous`; includes `sections/*.tex` in order |
| `current/macros.tex` | the draft machinery (below), names (`\sys`, `\secwasm`), maths macros, code environments |
| `current/sections/` | `00-abstract` … `10-conclusion`, `A-deviations`, `B-proofs` |
| `current/figures/` | TikZ figures |
| `current/biblio/refs.bib` | every entry verified against Crossref (Sept 2026) |
| `current/references/` | the PDFs cited (gitignored): SecWasm conference + full version with proofs, Rao's thesis, LeanWasm |
| `current/OUTLINE.md` | the pitch, contributions, assumptions, TODO inventory with fallbacks, questions for Abhi |
| `current/attic/` | the earlier "framework" draft (security automata, composition); not built; its framing is retired |

## The draft machinery

The draft is written as the strongest reasonable version, with every gap marked in place:

```latex
\tk{build}{what is missing}{the sentence we downgrade to if it is missed}
\tk{measure}{...}{...}   \tk{prove}{...}{...}   \tk{verify}{...}{...}   \tk{decide}{...}{...}
\assume{A1}{an assumption the section is written under}
\daniel{...} \abhi{...} \basin{...}   % editor notes
```

`grep -n 'tk{' current/sections/*.tex` is the work list. Set `\draftfalse` in `macros.tex` to hide
all boxes; nothing is substituted automatically, so resolve each by hand before the freeze.
