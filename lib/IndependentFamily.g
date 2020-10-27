FileEnumIndepSubsets:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"CanonicIndependentFamily");
ConvertListToGapSplitter:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"ConvertList_to_gap_splitter");


IndepFam_CreateFileInput:=function(SHV, MatrGRP, FileInput, FileFirst, FileFirstNb)
  local n, O, ListRepr, FuncFind, ListPermGens, PermGRP, eGen, eList, sValue, output, eElt, iS, eVect, iCol, eMin, eO, iSnew;
  Print("|SHV|=", Length(SHV), "  |GRP|=", Order(MatrGRP), "\n");
  n:=Length(SHV[1]);
  O:=Orbits(Group([-IdentityMat(n)]), SHV, OnPoints);
  ListRepr:=List(O, x->x[1]);
  FuncFind:=function(eVect)
    local pos;
    pos:=Position(ListRepr, eVect);
    if pos<>fail then
      return pos;
    fi;
    return Position(ListRepr, -eVect);
  end;
  ListPermGens:=[];
  for eGen in GeneratorsOfGroup(MatrGRP)
  do
    eList:=List(ListRepr, x->FuncFind(x*eGen));
    Add(ListPermGens, PermList(eList));
  od;
  PermGRP:=Group(ListPermGens);
  sValue:=Length(ListRepr);
  RemoveFileIfExist(FileInput);
  output:=OutputTextFile(FileInput, true);
  AppendTo(output, n, "\n");
  AppendTo(output, sValue, "\n");
  AppendTo(output, Order(PermGRP), "\n");
  for eElt in PermGRP
  do
    for iS in [1..sValue]
    do
      iSnew:=OnPoints(iS, eElt);
      AppendTo(output, " ", iSnew);
    od;
    AppendTo(output, "\n");
  od;
  for iS in [1..sValue]
  do
    eVect:=ListRepr[iS];
    for iCol in [1..n]
    do
      AppendTo(output, " ", eVect[iCol]);
    od;
    AppendTo(output, "\n");
  od;
  CloseStream(output);
  O:=Orbits(PermGRP, [1..sValue], OnPoints);
  RemoveFileIfExist(FileFirst);
  output:=OutputTextFile(FileFirst, true);
  for eO in O
  do
    eMin:=Minimum(eO);
    AppendTo(output, " ", eMin, "\n");
  od;
  CloseStream(output);
  output:=OutputTextFile(FileFirstNb, true);
  AppendTo(output, "1\n");
  AppendTo(output, Length(O), "\n");
  CloseStream(output);
  return ListRepr;
end;


IndepFam_GetAllSets:=function(SHV, MatrGRP, LimitNbRepresentatives)
  local n, FileInput, FileFirst, FileFirstNb, ListRepr, i, FileFirstI, FileFirstNbI, FileFirstJ, FileFirstNbJ, ThePrefix, TheCommand, FileINF, TheINF, nbCase, ListCases, ListNumberCases, ListFirstRepresentatives, iFile, eFileOrbit, ListOrbit, eOrbit, eFamVect, SNF, ListFactor, TheColl, pos, iCase;
  n:=Length(SHV[1]);
  FileInput:=Filename(POLYHEDRAL_tmpdir,"IndepFam.inp");
  FileFirst:=Filename(POLYHEDRAL_tmpdir,"IndepFam.list1");
  FileFirstNb:=Filename(POLYHEDRAL_tmpdir,"IndepFam.nb1");
  ListRepr:=IndepFam_CreateFileInput(SHV, MatrGRP, FileInput, FileFirst, FileFirstNb);
  for i in [2..n]
  do
    FileFirstI:=Filename(POLYHEDRAL_tmpdir,Concatenation("IndepFam.list", String(i-1)));
    FileFirstNbI:=Filename(POLYHEDRAL_tmpdir,Concatenation("IndepFam.nb", String(i-1)));
    FileFirstJ:=Filename(POLYHEDRAL_tmpdir,Concatenation("IndepFam.list", String(i)));
    FileFirstNbJ:=Filename(POLYHEDRAL_tmpdir,Concatenation("IndepFam.nb", String(i)));
    TheCommand:=Concatenation(FileEnumIndepSubsets, " ", FileInput, " ", FileFirstNbI, " ", FileFirstI, " ", FileFirstNbJ, " ", FileFirstJ);
    Exec(TheCommand);
  od;
  ThePrefix:=Filename(POLYHEDRAL_tmpdir,"ThePre");
  TheCommand:=Concatenation(ConvertListToGapSplitter, " ", ThePrefix, " 10000 ", FileFirstJ);
  Exec(TheCommand);
  #
  FileINF:=Concatenation(ThePrefix, "0");
  TheINF:=ReadAsFunction(FileINF)();
  nbCase:=TheINF[1];
  ListNumberCases:=[];
  ListCases:=[];
  ListFirstRepresentatives:=[];
  for iFile in [1..nbCase]
  do
    Print("iFile=", iFile, "/", nbCase, "\n");
    eFileOrbit:=Concatenation(ThePrefix, String(iFile));
    ListOrbit:=ReadAsFunction(eFileOrbit)();
    for eOrbit in ListOrbit
    do
      eFamVect:=ListRepr{eOrbit};
      SNF:=SmithNormalFormIntegerMat(eFamVect);
      ListFactor:=List([1..n], x->SNF[x][x]);
      TheColl:=Collected(ListFactor);
      pos:=Position(ListCases, TheColl);
      if pos<>fail then
        ListNumberCases[pos]:=ListNumberCases[pos]+1;
        if Length(ListFirstRepresentatives[pos])< LimitNbRepresentatives then
          Add(ListFirstRepresentatives[pos], eFamVect);
        fi;
      else
        Add(ListCases, TheColl);
        Add(ListNumberCases, 1);
        Add(ListFirstRepresentatives, [eFamVect]);
      fi;
    od;
    for iCase in [1..Length(ListCases)]
    do
      Print("iCase=", iCase, " TheColl=", ListCases[iCase], " nb=", ListNumberCases[iCase], "\n");
    od;
  od;
  RemoveFile(FileInput);
  for i in [1..n]
  do
    FileFirstI:=Filename(POLYHEDRAL_tmpdir,Concatenation("IndepFam.list", String(i)));
    FileFirstNbI:=Filename(POLYHEDRAL_tmpdir,Concatenation("IndepFam.nb", String(i)));
    RemoveFileIfExist(FileFirstI);
    RemoveFileIfExist(FileFirstNbI);
  od;  
  return rec(ListCases:=ListCases, ListRepr:=ListRepr, n:=n, 
             LimitNbRepresentatives:=LimitNbRepresentatives, 
             ListNumberCases:=ListNumberCases, 
             ListFirstRepresentatives:=ListFirstRepresentatives);
end;


IndepFam_PrintResult:=function(TheFileCases, TheRec)
  local output, nbCase, iCase, TheSeq, u, it, nbOrb, iOrb, eFamVect, eVect, j, ListOrbs, n;
  RemoveFileIfExist(TheFileCases);
  n:=TheRec.n;
  output:=OutputTextFile(TheFileCases, true);
  nbCase:=Length(TheRec.ListCases);
  AppendTo(output, "nbCase=", nbCase, "\n");
  for iCase in [1..nbCase]
  do
    AppendTo(output, "iCase=", iCase, "\n");
    TheSeq:=TheRec.ListCases[iCase];
    for u in TheSeq
    do
      for it in [1..u[2]]
      do
        AppendTo(output, " ", u[1]);
      od;
    od;
    AppendTo(output, "\n");
    AppendTo(output, "nb of occurring orbits=", TheRec.ListNumberCases[iCase], "\n");
    AppendTo(output, "selected representing orbits (at most ", TheRec.LimitNbRepresentatives, ")\n");
    ListOrbs:=TheRec.ListFirstRepresentatives[iCase];
    nbOrb:=Length(ListOrbs);
    for iOrb in [1..nbOrb]
    do
      AppendTo(output, "  orbit nr=", iOrb, "\n");
      eFamVect:=ListOrbs[iOrb];
      for eVect in eFamVect
      do
        AppendTo(output, "  ");
        for j in [1..n]
        do
          AppendTo(output, " ", eVect[j]);
        od;
        AppendTo(output, "\n");
      od;
    od;
  od;
  CloseStream(output);
end;
