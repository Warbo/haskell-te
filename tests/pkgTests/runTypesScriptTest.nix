defs: with defs; pkg:

testRec {
  justPkg = testRun "runTypesScript with pkg" null {} ''
              ${runTypesScript pkg null}
            '';
}
