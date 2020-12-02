#!/bin/sh

VERSION=2.6.1.1
CURRENT=$(agda -V | sed "s/Agda version \([^-]*\).*/\1/")

if ! type "agda" > /dev/null || [ ! "$CURRENT" = "$VERSION" ]; then
  cabal update
  cabal install alex happy cpphs
  cabal install Agda-${VERSION}
fi

rm -rf $HOME/.agda
mkdir -p $HOME/.agda
cp libraries $HOME/.agda/
cd $HOME/.agda/
wget https://github.com/agda/agda-stdlib/archive/v1.4.tar.gz
tar -xvzf v1.4.tar.gz
cd -
