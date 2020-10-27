kron:=function(Amat, Bmat)
  local nbColA, nbRowA, nbColB, nbRowB, iRowA, iColA, iRowB, iColB, iRow, iCol, RetMat, nbColProd, nbRowProd;
  nbColA:=Length(Amat[1]);
  nbRowA:=Length(Amat);
  nbColB:=Length(Bmat[1]);
  nbRowB:=Length(Bmat);
  nbColProd:=nbColA*nbColB;
  nbRowProd:=nbRowA*nbRowB;
  RetMat:=NullMat(nbRowProd, nbColProd);
  for iRowA in [1..nbRowA]
  do
    for iColA in [1..nbColA]
    do
      for iRowB in [1..nbRowB]
      do
        for iColB in [1..nbColB]
        do
          iRow:=iRowA + nbRowA*(iRowB-1);
	  iCol:=iColA + nbColA*(iColB-1);
	  RetMat[iRow][iCol]:=Amat[iRowA][iColA] * Bmat[iRowB][iColB];
        od;
      od;
    od;
  od;
  return RetMat;
end;


Jmatrix:=function(n)
  local RetMat, i, j;
  RetMat:=NullMat(n,n);
  for i in [1..n]
  do
    for j in [1..n]
    do
      RetMat[i][j]:=1;
    od;
  od;
  return RetMat;
end;


ColumnConcat:=function(Amat, Bmat)
  local nbColA, nbColB, nbRow, nbCol, RetMat, iRow, iCol;
  nbColA:=Length(Amat[1]);
  nbColB:=Length(Bmat[1]);
  nbRow:=Length(Amat);
  if nbRow<>Length(Bmat) then
    Error("Number of rows is inconsistent");
  fi;
  nbCol:=nbColA + nbColB;
  RetMat:=NullMat(nbRow, nbCol);
  for iRow in [1..nbRow]
  do
    for iCol in [1..nbColA]
    do
      RetMat[iRow][iCol]:=Amat[iRow][iCol];
    od;
    for iCol in [1..nbColB]
    do
      RetMat[iRow][iCol+nbColA]:=Bmat[iRow][iCol];
    od;
  od;
  return RetMat;
end;

RowConcat:=function(Amat, Bmat)
  local nbRowA, nbRowB, nbCol;
  nbRowA:=Length(Amat);
  nbRowB:=Length(Bmat);
  nbCol:=Length(Amat[1]);
  if nbCol<>Length(Bmat[1]) then
    Error("Number of column is inconsistent");
  fi;
  return Concatenation(Amat, Bmat);
end;

Matlab_Ones:=function(nbRow, nbCol)
  local RetMat, i, j;
  RetMat:=NullMat(nbRow,nbCol);
  for i in [1..nbRow]
  do
    for j in [1..nbCol]
    do
      RetMat[i][j]:=1;
    od;
  od;
  return RetMat;
end;


# We ape the localStrategies.m code.
# Only the option 0 and 1.
#
localStrategies:=function(scenario, option)
  local nbParties, strategies, i, eScenario, nbInputs, strat1party, j, siz, strat1party2, eMat1, eMat2, V, siz1, siz2;
  if option<>0 and option<>1 then
    Error("option should be 0 or 1");
  fi;
  nbParties:=Length(scenario);
  strategies:=[];
  for i in [1..nbParties]
  do
    eScenario:=scenario[i];
    Print("i=", i, " eScenario=", eScenario, "\n");
    nbInputs:=Length(eScenario);
    if option=1 then
      strat1party:=IdentityMat(eScenario[1]);
    fi;
    if option=0 then
      strat1party:=ColumnConcat(Matlab_Ones(eScenario[1],1), RowConcat(IdentityMat(eScenario[1]-1), NullMat(1,eScenario[1]-1)));
    fi;
    Print("strat1party\n");
    PrintArray(strat1party);
    for j in [2..nbInputs]
    do
      siz:=eScenario[j];
      if option=1 then
        strat1party2:=IdentityMat(siz);
      fi;
      if option=0 then
        strat1party2:=RowConcat(IdentityMat(siz-1), NullMat(1,siz-1));
      fi;
      Print("  j=", j, " siz=", siz, "\n");
      Print("strat1party2\n");
      PrintArray(strat1party2);
      siz1:=Length(strat1party);
      siz2:=Length(strat1party2);
      eMat1:=kron(strat1party, Matlab_Ones(siz2,1));
      eMat2:=kron(Matlab_Ones(siz1,1), strat1party2);
      strat1party:=ColumnConcat(eMat1, eMat2);
    od;
    Print("Insert strat1party\n");
    PrintArray(strat1party);
    Add(strategies, strat1party);
  od;
  V:=strategies[nbParties];
  for i in Reversed([1..nbParties-1])
  do
    V:=kron(V, strategies[i]);
  od;
  return V;
end;


