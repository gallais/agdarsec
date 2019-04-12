#!/bin/sh

VERSION=2.6.0

if ! type "agda" > /dev/null || [ ! `agda -V | sed "s/Agda version \([0-9\.]+\)//"` = "$VERSION" ]; then
  cabal update
  cabal install alex happy cpphs
  cabal install Agda-${VERSION}
  mkdir -p $HOME/.agda
  cp libraries $HOME/.agda/
  cd $HOME/.agda/
  wget https://github.com/agda/agda-stdlib/archive/v1.0.tar.gz
  tar -xvzf v1.0.tar.gz
  cd -
fi
