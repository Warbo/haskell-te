{ jq, lib, nth, parseJSON, runScript, writeScript }:
with builtins;
with lib;

rec {
  # Bash code to echo `count` numbers between `low` and `high`
  randNums = count: low: high: ''
    seq ${toString low} ${toString high} | shuf | head -n${toString count}
  '';

  # Return a random list of `count` numbers, between `low` and `high`
  randList = count: low: high: fromJSON (runScript { buildInputs = [ jq ]; } ''
    set -e

    # Cache-buster: ${toString currentTime}

    function rLoop() {
      ${randNums count low high}
    }
    rLoop | jq -s '.' > "$out"
  '');

  # Return a random sample of `count` elements from `list`
  randElems = list: count:
    let indices = randList count 1 (length list);
     in map (flip nth list) indices;

  # Return a random sample of `count` elements from the list of strings `list`.
  # For speed, we use Bash concatenate `list` elements with newlines, which won't work
  # for elements containing newlines.this will breaktreat each element as a line, which breaks the selection is done in Bash.
  randStrings = list: count:
    let elems = writeScript "rand-elems" (concatStringsSep "\n" list);
     in parseJSON (runScript { buildInputs = [ jq ]; } ''
          set -e
          echo 'Shuffling list...' 1>&2

          cat "${elems}"           |        # Each line is a list element
          shuf                     |        # Shuffle the elements
          head -n${toString count} |        # Take the first `count` elements
          jq -R '.'                |        # Wrap in quotes
          jq -s '.'                > "$out" # "Slurp" into an array and output

          echo 'Finished shuffling' 1>&2
  '');
}
