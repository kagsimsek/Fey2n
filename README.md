Mathematica notebook to compute the Feynman rules for dimension-2n Standard Model (Effective Field Theory) (SM(EFT)) in the Feynman gauge.

v0.1.1.

The vertex factors are printed out to a pdf.

Requires pdflatex and GNU version of sed.

Currently, only the case n = 2 is supported, hence the name Fey4 (as in "phi-4 theory").


Items to improve:

[x]	The DiracChain operator should be improved so as to contain 2n-fermion operators in the SMEFT.

[ ]	There should be a smarter way to extract the vertex types, which can indeed be done with a simple For loop, which I will do next probably.

[ ]	It sounds a bit advanced to me at the moment but the output should be universal.

[ ]	If we talk about a universal output, then the propagators should also be derived.

[ ]	The Faddeev-Popov particles, namely the ghosts, should also be included.

[ ]	If the code can perform the diagonalization, that would be great.

[ ]	Although not necessary, the Feynman diagrams would look classy.

[ ]	Currently, it requires a LaTeX distribution already installed and has been tested so far on Linux, using GNU sed. These dependencies, at least the latter, should be lifted. For instance, MacOS uses a different sed, so the HomeBrew version of it does the job. Well, Macs are overrated, anyways.
