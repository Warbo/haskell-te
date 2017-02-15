with import ./. {};

with rec {
  getData = cmd: stdenv.mkDerivation {
    name = "${cmd}-stabilise-data";
    buildInputs  = [ package ];
    buildCommand = ''
      SAMPLE_SIZES="5 10 15" REPS=30 ${cmd} > "$out"
    '';
};
{
  quickSpec = rec {
    data = getData "quickspecBench";
  };
  mlSpec = rec {
    data = getData "mlspecBench";
}
