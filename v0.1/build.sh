#!/bin/bash

cabal build
cabal haddock --executable

exit 0
