#!/bin/sh

VERSION=2.5.4.2

if ! type "agda" > /dev/null || [ ! `agda -V | sed "s/[^2]*//"` = "$VERSION" ]; then
  cabal update
  cabal install alex happy cpphs
  cabal install Agda-${VERSION}
  mkdir -p $HOME/.agda
  cp libraries-${VERSION} $HOME/.agda/
  cd $HOME/.agda/
  wget https://github.com/agda/agda-stdlib/archive/v0.17.tar.gz
  tar -xvzf v0.17.tar.gz
  cd -
fi
