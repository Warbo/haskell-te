{}:
with builtins;

rec {
  eqsVsTimeForKs = ks: pkgs:
    let points = listToAttrs (map (k: {
                   name  = k;
                   value = map (pkg: { eqs  = pkg.equationCount."${k}";
                                       time = pkg.totalWithTime."${k}"; }) pkgs;
                 }) ks);
        times = unique (fold (k: ts: (map (p: p.time) points."${k}") ++ ts)
                             []
                             (attrNames points));
     in trace "FIXME: not implemented" "";
}
