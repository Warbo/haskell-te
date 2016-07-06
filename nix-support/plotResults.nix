{ ourCheck, gnuplot, lib, runScript, storeResult, writeScript }:
with builtins;
with lib;

rec {

hasSD = any (r: length r == 3);

renderTable = x: y: rows:
  let renderCells = concatStringsSep "\t";
      renderRows  = concatStringsSep "\n";
      sdHead      = if hasSD rows then ["stddev"] else [];
      headRow     = [([x y] ++ sdHead)];
      result      = renderRows (map renderCells
                                    rows);
   in assert ourCheck "isList rows ${toJSON rows}"
                   (isList rows);

      assert ourCheck "all isList rows ${toJSON rows}"
                   (all isList rows);

      assert ourCheck "all (all isString) rows ${toJSON rows}"
                   (all (all isString) rows);

      assert ourCheck "Forcing renderTable result" (isString "${toJSON result}");
      result;

scatterPlot = tbl:
  let data        = mapAttrs (dataFile tbl.x tbl.y) tbl.series;
      dataFile    = x: y: series: rows:
                      let file = writeScript "scatter-${x}-${y}-${series}.tsv"
                                             (renderTable x y rows);
                       in { data = "${file}"; hasSD = hasSD rows; };
      dataLines   = map (n: let f  = data.${n}.data;
                                eb = if data.${n}.hasSD then "with errorbars"
                                                        else "";
                                in "'${f}' ${eb} title \"${n}\"")
                        (attrNames data);
      dataLine    = concatStringsSep ", " dataLines;
      scatterGnus = trace "scatterPlot: ${toJSON tbl}" (writeScript "scatter.gnus" ''
        set terminal png
        set output ofilename
        set yrange [0:*]
        set xrange [0:*]
        set xlabel "${tbl.x}"
        set ylabel "${tbl.y}"
        plot ${dataLine}
      '');
      scatterResult = addErrorContext
        "Running GNUPlot: Program ${toJSON scatterGnus}, Data ${toJSON data}"
        (runScript { buildInputs = [ gnuplot ]; } ''
          set -e
          gnuplot -e "ofilename='plot.png'" "${scatterGnus}"
          "${storeResult}" "plot.png" "$out"
        '');
   in if tbl.series == {}
         then null
         else assert ourCheck "Forcing scatterGnus"   (isString "${toJSON scatterGnus}");
              assert ourCheck "Forcing data"          (isString "${toJSON data}");
              assert ourCheck "Forcing scatterResult" (isString "${toJSON scatterResult}");
              addErrorContext "Plotting scatter chart" scatterResult;

# Mostly for tests
mkTbl = keyAttrs: dataAttrs:
  let joinCells = concatStringsSep "\t";
      joinRows  = concatStringsSep "\n";
      mkRow     = _: data: map (key: data."${key}") keys;

      keys = map (a: a.key)  keyAttrs;
      head = joinCells (map (a: a.name) keyAttrs);

      tblA = mapAttrs mkRow dataAttrs;
      tblL = map (n: joinCells tblA."${n}") (attrNames tblA);
   in joinRows ([head] ++ tblL);
}
