#!/bin/bash

IDRIS_PATH="$HOME/Desktop/idris/out/bin"

exec bash --rcfile <(
  echo '. $HOME/.bashrc'
  echo 'export PATH="'"$IDRIS_PATH"':$PATH"'
  echo 'eval "$(idris2 --bash-completion-script idris2)"'
  echo "alias idris2='rlwrap idris2'"
) -i
