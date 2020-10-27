FileMINISAT:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"minisat");
FileConvertMINISAToutput:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"MinisatToGAP");


PrintForSpectralLowerBound:=function(FileName, GRA)
  local output, iVert, LAdj, eAdj;
  RemoveFileIfExist(FileName);
  output:=OutputTextFile(FileName, true);
  AppendTo(output, GRA.order, "\n");
  for iVert in [1..GRA.order]
  do
    LAdj:=Adjacency(GRA, iVert);
    AppendTo(output, Length(LAdj));
    for eAdj in LAdj
    do
      AppendTo(output, " ", eAdj-1);
    od;
    AppendTo(output, "\n");
  od;
  CloseStream(output);
end;



GetSatisfiabilityForColoring:=function(GRA, nbColor)
  local MatrixIndex, n, i, eC, ListCNF, eCNF, fC, eAdj, pos1, pos2, pos;
  n:=GRA.order;
  MatrixIndex:=NullMat(n, nbColor);
  pos:=0;
  for i in [1..n]
  do
    for eC in [1..nbColor]
    do
      pos:=pos+1;
      MatrixIndex[i][eC]:=pos;
    od;
  od;
  ListCNF:=[];
  #
  # At least one color should be selected for each vertex
  #
  for i in [1..n]
  do
    eCNF:=[];
    for eC in [1..nbColor]
    do
      Add(eCNF, MatrixIndex[i][eC]);
    od;
    Add(ListCNF, eCNF);
  od;
  #
  # For each vertex at most one color should be selected
  #
  for i in [1..n]
  do
    for eC in [1..nbColor]
    do
      for fC in [eC+1..nbColor]
      do
        pos1:=MatrixIndex[i][eC];
        pos2:=MatrixIndex[i][fC];
	Add(ListCNF, [-pos1, -pos2]);
      od;
    od;
  od;
  #
  # for each edge we should not have the same color on both
  #
  for i in [1..n]
  do
    for eAdj in Adjacency(GRA, i)
    do
      if eAdj > i then
        for eC in [1..nbColor]
	do
	  pos1:=MatrixIndex[i][eC];
	  pos2:=MatrixIndex[eAdj][eC];
	  Add(ListCNF, [-pos1, -pos2]);
	od;
      fi;
    od;
  od;
  #
  # Returning the system
  #
  return ListCNF;
end;







GetColoring:=function(SolCNF, nbVert, nbColor)
  local MatrixIndex, pos, i, eC, ThePartition, VectorColoring;
  if SolCNF.result=false then
    return false;
  fi;
  MatrixIndex:=NullMat(nbVert, nbColor);
  pos:=0;
  for i in [1..nbVert]
  do
    for eC in [1..nbColor]
    do
      pos:=pos+1;
      MatrixIndex[i][eC]:=pos;
    od;
  od;
  ThePartition:=[];
  for eC in [1..nbColor]
  do
    Add(ThePartition, []);
  od;
  VectorColoring:=ListWithIdenticalEntries(nbVert, -1);
  for i in [1..nbVert]
  do
    for eC in [1..nbColor]
    do
      pos:=MatrixIndex[i][eC];
      if SolCNF.sat[pos]=1 then
        VectorColoring[i]:=eC;
	Add(ThePartition[eC], i);
      fi;
    od;
  od;
  return rec(ThePartition:=ThePartition, VectorColoring:=VectorColoring);
end;




GetListCNFforbiddingSpecificColoring:=function(nbVert, nbColor, SpecificColoring)
  local MatrixIndex, pos, i, eC, eCNF, iVert, eColor;
  MatrixIndex:=NullMat(nbVert, nbColor);
  pos:=0;
  for i in [1..nbVert]
  do
    for eC in [1..nbColor]
    do
      pos:=pos+1;
      MatrixIndex[i][eC]:=pos;
    od;
  od;
  eCNF:=[];
  for iVert in [1..nbVert]
  do
    eColor:=SpecificColoring[iVert];
    pos:=MatrixIndex[iVert][eColor];
    Add(eCNF, [-pos]);
  od;
  return [eCNF];
end;



GetListCNFspecifyingColorSomeVertices:=function(nbVert, nbColor, ListPair)
  local MatrixIndex, pos, i, eC, eCNF, iVert, eVert, eColor, ListCNF, ePair;
  MatrixIndex:=NullMat(nbVert, nbColor);
  pos:=0;
  for i in [1..nbVert]
  do
    for eC in [1..nbColor]
    do
      pos:=pos+1;
      MatrixIndex[i][eC]:=pos;
    od;
  od;
  ListCNF:=[];
  for ePair in ListPair
  do
    eVert:=ePair.eVert;
    eColor:=ePair.eColor;
    pos:=MatrixIndex[eVert][eColor];
    Add(ListCNF, [pos]);
  od;
  return ListCNF;
end;





GetCodeTilingSatisfiabilityConstraints:=function(GRP, ListEltTile)
  local ListElt, eElt, nbElt, eGen, eEltG, ListPairPack, iElt, jElt, TheInt, ListCovering, i, fElt, pos, ListCNF, ePairPack, iElt1, iElt2, eCNF, eCovering;
  ListElt:=[];
  for eElt in GRP
  do
    Add(ListElt, eElt);
  od;
  nbElt:=Length(ListElt);
  for eGen in GeneratorsOfGroup(GRP)
  do
    for eElt in ListEltTile
    do
      eEltG:=Inverse(eGen)*eElt*eGen;
      if Position(ListEltTile, eElt)=fail then
        Error("ListEltTile does not appear to be invariant by conjugation");
      fi;
    od;
  od;
  ListPairPack:=[];
  for iElt in [1..nbElt-1]
  do
    for jElt in [iElt+1..nbElt]
    do
      TheInt:=Intersection(Set(ListElt[iElt]*ListEltTile), Set(ListElt[jElt]*ListEltTile));
      if Length(TheInt)>0 then
        Add(ListPairPack, [iElt, jElt]);
      fi;
    od;
  od;
  ListCovering:=[];
  for i in [1..nbElt]
  do
    Add(ListCovering, []);
  od;
  for iElt in [1..nbElt]
  do
    for fElt in ListElt[iElt]*ListEltTile
    do
      pos:=Position(ListElt, fElt);
      Add(ListCovering[pos], iElt);
    od;
  od;
  ListCNF:=[];
  for ePairPack in ListPairPack
  do
    iElt1:=ePairPack[1];
    iElt2:=ePairPack[2];
    eCNF:=[-iElt1, -iElt2];
    Add(ListCNF, eCNF);
  od;
  for eCovering in ListCovering
  do
    Add(ListCNF, eCovering);
  od;
  return ListCNF;  
end;




CubeTilingCaseItohModel:=function(n)
  local ListElt, nbElt, GetPerm, ListPerm, i, eVect, GRP, ListEltTile;
  ListElt:=BuildSet(n, [0..3]);
  nbElt:=Length(ListElt);
  GetPerm:=function(eVect)
    local eList, iElt, eVect2, eVect3, pos;
    eList:=ListWithIdenticalEntries(nbElt,0);
    for iElt in [1..nbElt]
    do
      eVect2:=ListElt[iElt] + eVect;
      eVect3:=eVect2 mod 4;
      pos:=Position(ListElt, eVect3);
      eList[iElt]:=pos;
    od;
    return PermList(eList);
  end;
  ListPerm:=[];
  for i in [1..n]
  do
    eVect:=ListWithIdenticalEntries(n,0);
    eVect[i]:=1;
    Add(ListPerm, GetPerm(eVect));
  od;
  GRP:=Group(ListPerm);
  ListEltTile:=List(BuildSet(n, [0..1]), GetPerm);
  return rec(GRP:=GRP, ListEltTile:=ListEltTile);
end;



SolveCNF:=function(ListCNF)
  local FileIn, FileErr, FileOut, FileRes, nbCNF, nbVAR, eCNF, LVal, output, eVal, TheCommand, TheRes;
  FileIn:=Filename(POLYHEDRAL_tmpdir,"Minisat.in");
  FileErr:=Filename(POLYHEDRAL_tmpdir,"Minisat.err");
  FileOut:=Filename(POLYHEDRAL_tmpdir,"Minisat.out");
  FileRes:=Filename(POLYHEDRAL_tmpdir,"Minisat.res");
  nbCNF:=Length(ListCNF);
  nbVAR:=0;
  for eCNF in ListCNF
  do
    LVal:=List(eCNF, AbsInt);
    nbVAR:=Maximum(nbVAR, Maximum(LVal));
  od;
  output:=OutputTextFile(FileIn, true);
  AppendTo(output, "p cnf ", nbVAR, " ", nbCNF, "\n");
  for eCNF in ListCNF
  do
    for eVal in eCNF
    do
      AppendTo(output, eVal, " ");
    od;
    AppendTo(output, "0\n");
  od;
  CloseStream(output);
  TheCommand:=Concatenation(FileMINISAT, " ", FileIn, " ", FileOut, " > ", FileErr);
  Exec(TheCommand);
  TheCommand:=Concatenation(FileConvertMINISAToutput, " ", FileOut, " ", FileRes);
  Exec(TheCommand);
  TheRes:=ReadAsFunction(FileRes)();
  RemoveFileIfExist(FileIn);
  RemoveFileIfExist(FileErr);
  RemoveFileIfExist(FileOut);
  RemoveFileIfExist(FileRes);
  return TheRes;
end;


MINISAT_ChromaticNumber:=function(GRA)
  local CliqueNr, nbColor, ListCNF, SolCNF;
  CliqueNr:=Maximum(List(CompleteSubgraphs(GRA), Length));
  nbColor:=CliqueNr;
  while(true)
  do
    Print("Trying nbColor=", nbColor, "\n");
    ListCNF:=GetSatisfiabilityForColoring(GRA, nbColor);
    SolCNF:=SolveCNF(ListCNF);
    if SolCNF.result then
      return nbColor;
    fi;
    nbColor:=nbColor+1;
  od;
end;


SolveCNF_number:=function(ListCNF, nbMax)
  local ListSolution, ListCNFcomplex, eCNF, eSol, fCNF, len, iVert, SolCNF;
  ListSolution:=[];
  while(true)
  do
    ListCNFcomplex:=[];
    for eCNF in ListCNF
    do
      Add(ListCNFcomplex, eCNF);
    od;
    for eSol in ListSolution
    do
      fCNF:=[];
      len:=Length(eSol);
      for iVert in [1..len]
      do
        if eSol[iVert]=1 then
	  Add(fCNF, -iVert);
	else
	  Add(fCNF, iVert);
	fi;
      od;
      Add(ListCNFcomplex, fCNF);
    od;
    SolCNF:=SolveCNF(ListCNFcomplex);
    Print("SolCNF obtained\n");
    if SolCNF.result=false then
      break;
    fi;
    if nbMax>0 then
      if Length(ListSolution)=nbMax then
        break;
      fi;
    fi;
  od;
  return ListSolution;
end;
