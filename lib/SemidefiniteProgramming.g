FileCsdpOutputRead:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"CsdpOutRead");


ReadCsdpOutput:=function(eFileOut)
  local eFileRef, TheResult;
  eFileRef:=Filename(POLYHEDRAL_tmpdir,"Csdp.ref");
  RemoveFileIfExist(eFileRef);
  Exec(FileCsdpOutputRead, " ", eFileOut, " > ", eFileRef);
  TheResult:=ReadAsFunction(eFileRef)();
  RemoveFileIfExist(eFileRef);
  return TheResult;
end;





ReadCsdpInputProgram:=function(eFile)
  local TheList, nbRHS, nbMat, ListSignDimension, ListDimension, ListTypeBlock, iMat, eTypeBlock, ListRhs, iLine, ListLines, eLine, eEnt;
  TheList:=ReadVectorFile(eFile);
  nbRHS:=TheList[1][1];
  nbMat:=TheList[2][1];
  ListSignDimension:=TheList[3];
  nbMat:=Length(ListSignDimension);
  ListDimension:=[];
  ListTypeBlock:=[];
  for iMat in [1..nbMat]
  do
    ListDimension[iMat]:=AbsInt(ListSignDimension[iMat]);
    if ListSignDimension[iMat]>0 then
      eTypeBlock:="plus";
    else
      eTypeBlock:="minus";
    fi;
    ListTypeBlock[iMat]:=eTypeBlock;
  od;
  ListRhs:=TheList[4];
  ListLines:=[];
  for iLine in [5..Length(TheList)]
  do
    eLine:=TheList[iLine];
    eEnt:=rec(idx:=eLine[1], iMat:=eLine[2], i:=eLine[3], j:=eLine[4], eVal:=eLine[5]);
    Add(ListLines, eEnt);
  od;
  return rec(ListStringComment:=[],
             nbBlock:=nbMat, 
             ListRhs:=ListRhs,
             ListTypeBlock:=ListTypeBlock,
             ListDimension:=ListDimension,
             ListLines:=ListLines);
end;

CreateSemidefiniteProgramThetaNumberGraph:=function(eG)
  local n, ListTypeBlock, ListDimension, nbBlock, ListLines, ListRhs, i, j, eAdj, eEnt, iEqua;
  n:=eG.order;
  ListTypeBlock:=["plus"];
  ListDimension:=[n];
  nbBlock:=1;
  #
  ListLines:=[];
  ListRhs:=[];
  #
  # The Term Tr(BJ)
  for i in [1..n]
  do
    for j in [i..n]
    do
      eEnt:=rec(idx:=0, iMat:=1, i:=i, j:=j, eVal:=1);
      Add(ListLines, eEnt);
    od;
  od;
  #
  # The equalities Bij=0 if ij in E
  iEqua:=0;
  for i in [1..n]
  do
    for eAdj in Adjacency(eG, i)
    do
      if eAdj > i then
        iEqua:=iEqua+1;
	Add(ListRhs, 0);
	eEnt:=rec(idx:=iEqua, iMat:=1, i:=i, j:=eAdj, eVal:=1);
	Add(ListLines, eEnt);
      fi;
    od;
  od;
  #
  # The equalities Tr(X) = 1
  iEqua:=iEqua+1;
  Add(ListRhs, 1);
  for i in [1..n]
  do
    eEnt:=rec(idx:=iEqua, iMat:=1, i:=i, j:=i, eVal:=1);
    Add(ListLines, eEnt);
  od;
  #
  return rec(ListStringComment:=[],
             nbBlock:=nbBlock, 
             ListRhs:=ListRhs,
             ListTypeBlock:=ListTypeBlock,
             ListDimension:=ListDimension,
             ListLines:=ListLines);
end;




CheckDuplication:=function(ListLines)
  local ListLinesRed, eEnt, eEntRed, iWrt, jWrt;
  ListLinesRed:=[];
  for eEnt in ListLines
  do
    if eEnt.i<eEnt.j then
      iWrt:=eEnt.i;
      jWrt:=eEnt.j;
    else
      iWrt:=eEnt.j;
      jWrt:=eEnt.i;
    fi;
    eEntRed:=rec(idx:=eEnt.idx, iMat:=eEnt.iMat, i:=iWrt, j:=jWrt);
    Add(ListLinesRed, eEntRed);
  od;
  return Length(Set(ListLinesRed))=Length(ListLinesRed);
end;



#
# The factorizations of the matrices are of the form
# A = t(P) B P
# with P = [v1, ...., vL]
# 
MappingOfSdpProgram:=function(TheRecordCsdpIn, ListMatrixFactorization)
  local nbMatIn, ListDimFactorization, iMat, eDim, ListDimensionOutput, ListTypeBlockOutput, MappingDir, MappingRev, idx, MapSingleEntry, SimplifyListEnt, nbRHS, ListLinesOutput, ListRhsOutput, iRHSfinal, iRHS, ListMatch, NewListEnt, eEnt, ListEntFinal, eEntFinal, nbBlockOutput, ListEntFinal_objective, ListCompleteSystem, TheRec, eRec, FactorTwoElimination;
  if CheckDuplication(TheRecordCsdpIn.ListLines)=false then
    Print("We have duplication in the input\n");
    Error("Please correct your input file");
  fi;
  nbMatIn:=Length(TheRecordCsdpIn.ListDimension);
  ListDimFactorization:=List(ListMatrixFactorization, x->Length(x.eMat));
  if Length(ListDimFactorization)<>nbMatIn then
    Error("Inconsistency in the input for nbMatIn");
  fi;
  for iMat in [1..nbMatIn]
  do
    if ListMatrixFactorization[iMat].eDim<>TheRecordCsdpIn.ListDimension[iMat] then
      Error("Dimension error in the input");
    fi;
  od;
  Print("We have matrix information\n");
  ListDimensionOutput:=[];
  ListTypeBlockOutput:=[];
  MappingDir:=ListWithIdenticalEntries(nbMatIn, -1);
  MappingRev:=[];
  idx:=0;
  for iMat in [1..nbMatIn]
  do
    if ListDimFactorization[iMat]>0 then
      idx:=idx+1;
      Add(MappingRev, iMat);
      MappingDir[iMat]:=idx;
      Add(ListDimensionOutput, ListDimFactorization[iMat]);
      if TheRecordCsdpIn.ListTypeBlock[iMat]="plus" then
        Add(ListTypeBlockOutput, "plus");
      else
        Add(ListTypeBlockOutput, "minus");
      fi;
    fi;
  od;
  nbBlockOutput:=Length(MappingRev);
  Print("We have ListDimensionOutput / ListTypeBlockOutput\n");
  MapSingleEntry:=function(eEnt)
    local ListNewEnt, iMat, iMatMap, eDim, iOrig, jOrig, i, j, eVal1, eVal2, eVal, iWrt, jWrt, eNewEnt, eMult;
    ListNewEnt:=[];
    iMat:=eEnt.iMat;
    iMatMap:=MappingDir[iMat];
    eDim:=ListDimFactorization[iMat];
    iOrig:=eEnt.i;
    jOrig:=eEnt.j;
    for i in [1..eDim]
    do
      for j in [1..eDim]
      do
        eVal1:=ListMatrixFactorization[iMat].eMat[i][iOrig];
        eVal2:=ListMatrixFactorization[iMat].eMat[j][jOrig];
	if i<j then
	  iWrt:=i;
	  jWrt:=j;
	else
	  iWrt:=j;
	  jWrt:=i;
	fi;
	if iOrig=jOrig then
	  eMult:=1;
	else
	  eMult:=2;
	fi;
        eVal:=eVal1 * eVal2 * eEnt.eVal * eMult;
	if eVal<>0 then
          eNewEnt:=rec(iMat:=iMatMap, i:=iWrt, j:=jWrt, eVal:=eVal);
          Add(ListNewEnt, eNewEnt);
        fi;
      od;
    od;
    return ListNewEnt;
  end;
  SimplifyListEnt:=function(ListEnt)
    local ListEntRed, ListEntFinal, SetEntFinal, SetEntRed, eEntRed, LPos, eVal, eEntFinal;
    ListEntRed:=List(ListEnt, x->rec(iMat:=x.iMat, i:=x.i, j:=x.j));
    ListEntFinal:=[];
    SetEntRed:=Set(ListEntRed);
    for eEntRed in SetEntRed
    do
      LPos:=Filtered([1..Length(ListEnt)], x->ListEntRed[x]=eEntRed);
      eVal:=Sum(List(LPos, x->ListEnt[x].eVal));
      if eVal<>0 then
        eEntFinal:=rec(iMat:=eEntRed.iMat, i:=eEntRed.i, j:=eEntRed.j, eVal:=eVal);
        Add(ListEntFinal, eEntFinal);
      fi;
    od;
    return ListEntFinal;
  end;
  nbRHS:=Length(TheRecordCsdpIn.ListRhs);
  iRHSfinal:=0;
  ListCompleteSystem:=[];
  for iRHS in [0..nbRHS]
  do
    Print("iRHS=", iRHS, " / ", nbRHS, "\n");
    ListMatch:=Filtered(TheRecordCsdpIn.ListLines, x->x.idx=iRHS);
    NewListEnt:=[];
    for eEnt in ListMatch
    do
      Append(NewListEnt, MapSingleEntry(eEnt));
    od;
    ListEntFinal:=SimplifyListEnt(NewListEnt);
    if Length(ListEntFinal)>0 then
      if iRHS=0 then
        ListEntFinal_objective:=ListEntFinal;
      else
        TheRec:=rec(eRHS:=TheRecordCsdpIn.ListRhs[iRHS], ListEntFinal:=ListEntFinal);
	Add(ListCompleteSystem, TheRec);
      fi;
    fi;
  od;
  FactorTwoElimination:=function(eEntIn)
    local eMult;
    if eEntIn.i=eEntIn.j then
      eMult:=1;
    else
      eMult:=1/2;
    fi;
    return rec(idx:=eEntIn.idx, iMat:=eEntIn.iMat, i:=eEntIn.i, j:=eEntIn.j, eVal:=eMult*eEntIn.eVal);
  end;
  ListLinesOutput:=[];
  ListRhsOutput:=[];
  for eEntFinal in ListEntFinal_objective
  do
    eEntFinal.idx:=0;
    Add(ListLinesOutput, FactorTwoElimination(eEntFinal));
  od;
  iRHSfinal:=0;
  for eRec in ListCompleteSystem
  do
    iRHSfinal:=iRHSfinal+1;
    Add(ListRhsOutput, eRec.eRHS);
    for eEntFinal in eRec.ListEntFinal
    do
      eEntFinal.idx:=iRHSfinal;
      Add(ListLinesOutput, FactorTwoElimination(eEntFinal));
    od;
  od;
  return rec(ListStringComment:=[],
             nbBlock:=nbBlockOutput, 
             ListRhs:=ListRhsOutput,
             ListLines:=ListLinesOutput,
             ListDimension:=ListDimensionOutput,
             ListTypeBlock:=ListTypeBlockOutput);
end;






# TheRecordCsdp contains the following entries
# ---ListStringCommend, a comment to the SDPA.
# ---ListRhs, the list of right hand side.
# ---ListDimension (the dimension of the matrices.
#                   if negative, then the matrix is diagonal)
# ---ListTypeBlock (whether the block is positive
# ---ListLines : The list of entries in the format [iIneq, iMat, i, j, eCoeff]
#     The inequalities are of the form a + b + c >= RHS
# ---
WriteFileCsdp:=function(eFile, TheRecordCsdp, PrintFrac)
  local output, eLineStr, nbBlock, nbBlockEff, iBlock, eVal, eRec, idx, iMat, i, j, nbRhs, PrintVal;
  RemoveFileIfExist(eFile);
  output:=OutputTextFile(eFile, true);
  for eLineStr in TheRecordCsdp.ListStringComment
  do
    AppendTo(output, "* ", eLineStr);
  od;
  nbRhs:=Length(TheRecordCsdp.ListRhs);
  AppendTo(output, Length(TheRecordCsdp.ListRhs), "\n");
  nbBlock:=TheRecordCsdp.nbBlock;
  if TheRecordCsdp.ListDimension[nbBlock]=0 then
    nbBlockEff:=nbBlock-1;
  else
    nbBlockEff:=nbBlock;
  fi;
  AppendTo(output, nbBlockEff, "\n");
  # ListDimension specifies 
  for iBlock in [1..nbBlock]
  do
    if TheRecordCsdp.ListDimension[iBlock]>0 then
      if TheRecordCsdp.ListTypeBlock[iBlock]="plus" then
        AppendTo(output, " ", TheRecordCsdp.ListDimension[iBlock]);
      else
        AppendTo(output, " -", TheRecordCsdp.ListDimension[iBlock]);
      fi;
    fi;
  od;
  PrintVal:=function(TheVal)
    if PrintFrac then
      AppendTo(output, TheVal);
    else
      AppendTo(output, GetFractionAsReal(TheVal));
    fi;
  end;
  AppendTo(output, "\n");
  for eVal in TheRecordCsdp.ListRhs
  do
    AppendTo(output, " ");
    PrintVal(eVal);
  od;
  AppendTo(output, "\n");
  for eRec in TheRecordCsdp.ListLines
  do
    idx:=eRec.idx; # This is actually the index of the inequality.
    iMat:=eRec.iMat;
    i:=eRec.i;
    j:=eRec.j;
    eVal:=eRec.eVal;
    AppendTo(output, idx, " ", iMat, " ", i, " ", j, " ");
    PrintVal(eVal);
    AppendTo(output, "\n");
  od;
  CloseStream(output);
end;
