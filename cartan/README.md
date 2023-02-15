# quad-cartan
Code to accompany the paper "Quadratic points on non-split Cartan modular curves" by Philippe Michaud-Jacobs (Michaud-Rodgers).
The paper is written under my previous surname, Michaud-Rodgers.

The paper is available on arXiv here: https://arxiv.org/abs/2011.00590.
The published version of the paper is available here: https://doi.org/10.48550/arXiv.2011.00590.

The repository contains the following files (more description is contained within each file):

- eqn_data.m contains equations for models and maps,
- model.m obtains a new model for X_ns(13),
- saturation.m carries out the saturation tests,
- saturation_output.txt contains the output of the saturation.m file,
- sieve.m carries out the sieving step,
- sieve_output.txt contains the output of the sieve.m file.

The code in this branch (main) of the repository differs from the version of the code originally associated with the published version of the paper. The notation in this branch matches that of the paper more closely, certain (minor) errors have been corrected, and more information and output has been included throughout. The code has also been simplified in many places compared to the original version. If you do wish to see the original code, it is available in the original-paper branch at the following link: https://github.com/michaud-jacobs/quad-cartan/tree/original-paper.
