This modifies the code of Martin Escardo's HoTT-UF-Agda lecture notes
(about 10k lines with no comments) to not mention any specific
universe, in particular the first one.

This was more difficult than expected, but possible.

This directory contains both the original files (with the comments all
removed) and the rewritten files (with the suffix "-new"). There are
all diff files.

We still use U_0 in some places, but now this is a universe
*variable*, rather than the name of the first universe.
