# LNCS submission manuscript

This directory contains a separate, condensed submission manuscript. It does
not replace or modify the original `paper.tex` / `paper.pdf` pair.

The class and bibliography-style files are unmodified copies from Springer's
official **LaTeX2e Proceedings Template**, downloaded from the LNCS author
information page on 2026-09-26. The class identifies itself as
`llncs 2026/09/03 v2.25`.

Build from the repository root:

```bash
make paper-lncs
```

The build runs `pdflatex` twice with `-halt-on-error`. The resulting
`paper-lncs.pdf` is eight LNCS pages and contains no undefined references,
LaTeX warnings, overfull boxes, or underfull boxes in the checked build log.

SHA-256 checksums for the source, output, and downloaded template files are
recorded in `SHA256SUMS`.
