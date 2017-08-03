LUDecomp[mat_] := 
  With[{lu = LUDecomposition[mat][[1]]}, {LowerTriangularize[lu, -1] +
      IdentityMatrix[Length[mat]], UpperTriangularize[lu]}];
