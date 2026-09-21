# A Formalized Foundation for Research in Untyped Lambda Calculus
## (cas-sc build)

Same paper as the `elsarticle` build, typeset with Elsevier's newer
`cas-sc`/`cas-dc` classes (the "Complex Article Service" workflow
templates), vendored here from the official bundle
(https://github.com/yaoyz96/els-cas-templates, mirroring CTAN's
`els-cas-templates`).

## Build

    make            # produces main.pdf (single column, cas-sc)
    make clean      # remove intermediate files
    make cleanall   # also remove main.pdf

To try the double-column layout instead, swap the `\documentclass`
line in `main.tex` from `cas-sc` to `cas-dc` (both classes are
vendored here).

## Two real bugs fixed here (not stylistic choices)

1. **Missing `natbib`.** `cas-sc.cls` does not load `natbib` itself —
   the official template loads it manually right after
   `\documentclass`. Without it, `\bibsep` (a natbib length) is
   undefined and the document fails at `\begin{document}`. Fixed by
   adding `\usepackage[numbers]{natbib}` in `main.tex`.

2. **Short-abstract/long-keyword-list overlap.** The class puts
   keywords in a narrow (`0.25\textwidth`) sidebar next to the
   abstract, and starts the body text based on the abstract column's
   height only, not the taller of the two columns. With a
   one-line placeholder abstract next to a long keyword list, the
   sidebar is taller than the abstract and "1. Introduction" starts
   overlapping the keywords. This is what was breaking your build —
   not a class bug in the usual sense, but an edge case that a
   realistic-length abstract (a sentence or two longer than the
   keyword column) avoids entirely, which is what's used here.
   (The class also ships a `longmktitle` option that documentation
   suggests is for long front matter, but in the currently
   vendored release it calls `\vbox_unpack_clear:N`, an expl3
   primitive renamed to `\vbox_unpack_drop:N` in current LaTeX3
   kernels -- it errors out on a modern TeX Live. Not needed once
   the abstract is a realistic length, so left unused here.)

## Which template does TCS actually want: elsarticle or cas-sc/cas-dc?

Honestly: I could not fully verify this. Elsevier's main LaTeX
instructions page names `elsarticle` as the primary manuscript
class and lists the CAS classes as an "additional" option for
journals on their newer CAS production workflow -- but which one a
specific journal's editorial system expects is stated in that
journal's own Guide for Authors, and I wasn't able to load Theoretical
Computer Science's specific guide (it's behind a page that blocked
automated fetches). Both classes here are genuinely current, official
Elsevier releases, not reconstructions -- this isn't a case of one
being "correct" and the other fake.

The reliable way to settle it: when you start a submission on TCS's
Editorial Manager, the submission portal / Guide for Authors
typically links a template specific to that journal. That link is
the actual answer. Until then, both builds are here so you're not
blocked either way.
