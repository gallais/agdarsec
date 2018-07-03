#!/bin/sh
if ! type "agda" > /dev/null || [ ! `agda -V | sed "s/[^2]*//"` = "2.5.1" ]; then
  cabal update
  cabal install alex happy cpphs
  cabal install Agda-2.5.4
  mkdir -p $HOME/.agda
  cp libraries-2.5.4 $HOME/.agda/
  cd $HOME/.agda/
  wget https://github.com/agda/agda-stdlib/archive/v0.16.tar.gz
  tar -xvzf v0.16.tar.gz
  cd -
fi
