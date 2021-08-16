## Instructions
Clone and build CBMC with RRA before running RRA proofs:
```console
git clone git@github.com:zlfben/cbmc.git
git checkout rra-dynamic-develop
cd cbmc
cmake -S . -Bbuild -GNinja -DWITH_JBMC=OFF
cd build
ninja
```
Then re-write CBMC_BIN_DIR in "./run.sh" to direct to the "cbmc/build/bin" folder.
