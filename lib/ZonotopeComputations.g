FileMinkSum:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"minkSum");
FileNudifyMink:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"NudifyMinkovskiOutput");


ZONOTOP_DimensionalOrdering:=function(ListVect)
  local NewListVect, n, nbVect, rMat, ListIdx, i, eSet, h, fSet;
  NewListVect:=[ListVect[1]];
  n:=Length(ListVect[1]);
  nbVect:=Length(ListVect);
  rMat:=[ListVect[1]];
  ListIdx:=ListWithIdenticalEntries(nbVect,1);
  ListIdx[1]:=0;
  for i in [2..n]
  do
    eSet:=Filtered([1..nbVect], x->ListIdx[x]=1);
    h:=eSet[1];
    Add(rMat, ListVect[h]);
    fSet:=Filtered(eSet, x->RankMat(Concatenation(rMat, [ListVect[x]]))=i);
    Append(NewListVect, ListVect{fSet});
    ListIdx{fSet}:=ListWithIdenticalEntries(Length(fSet),0);
  od;
  return NewListVect;
end;



ZONOTOP_ListAllSummation:=function(ListVect)
  local n, nbVect, ListSolution, iVect, PreListSolution, eVect, eVal, fVect;
  n:=Length(ListVect[1]);
  nbVect:=Length(ListVect);
  ListSolution:=[ListWithIdenticalEntries(n,0)];
  for iVect in [1..nbVect]
  do
    PreListSolution:=[];
    for eVect in ListSolution
    do
      for eVal in [-1,1]
      do
        fVect:=eVect+eVal*ListVect[iVect];
        Add(PreListSolution, fVect);
      od;
    od;
    ListSolution:=Set(PreListSolution);
    Print("iVect=", iVect, "/", nbVect, " |ListSolution|=", Length(ListSolution), "\n");
  od;
  Print("Finished, we have |ListSolution|=", Length(ListSolution), "\n");
  return ListSolution;
end;


ZONOTOP_GetVertices:=function(ListVect, GRPmatr)
  local n, nbVect, NewListVect, ListVectSum, EXT, NewListGens, eGen, ePerm, GRPperm, BoundingSet, eSetRelevant;
  n:=Length(ListVect[1]);
  nbVect:=Length(ListVect);
  NewListVect:=ZONOTOP_DimensionalOrdering(ListVect);
  ListVectSum:=ZONOTOP_ListAllSummation(NewListVect);
  EXT:=List(ListVectSum, x->Concatenation([1], x));
  NewListGens:=[];
  for eGen in GeneratorsOfGroup(GRPmatr)
  do
    ePerm:=SortingPerm(ListVectSum*eGen);
    Add(NewListGens, ePerm);
  od;
  GRPperm:=Group(NewListGens);
  Print("We have GRPperm\n");
  BoundingSet:=[];
  eSetRelevant:=EliminationByRedundancyEquivariant(EXT, BoundingSet, GRPperm).eSetSelect;
  return EXT{eSetRelevant};
end;



MINKSum_ByWeibelFukuda:=function(ListEXT)
  local FileInp, FileOut, FileLog, FileExt, n, output, PrintLine, eVect, TheCommand, TheReply, EXT, IsFirst, eEXT;
  n:=Length(ListEXT[1][1]);
  if Length(ListEXT)=1 then
    return ListEXT[1];
  fi;
  FileInp:=Filename(POLYHEDRAL_tmpdir,"Mink.inp");
  FileOut:=Filename(POLYHEDRAL_tmpdir,"Mink.out");
  FileLog:=Filename(POLYHEDRAL_tmpdir,"Mink.log");
  FileExt:=Filename(POLYHEDRAL_tmpdir,"Mink.ext");
  RemoveFileIfExist(FileInp);
  RemoveFileIfExist(FileOut);
  RemoveFileIfExist(FileLog);
  RemoveFileIfExist(FileExt);
  output:=OutputTextFile(FileInp, true);
  AppendTo(output, "[\n");
  PrintLine:=function(eLine)
    local i;
    AppendTo(output, "[");
    for i in [1..n]
    do
      if i>1 then
        AppendTo(output, ",");
      fi;
      AppendTo(output, eLine[i]);
    od;
    AppendTo(output, "]");
  end;
#  Print("|ListEXT|=", Length(ListEXT), "\n");
  for EXT in ListEXT
  do
    AppendTo(output, "[");
    IsFirst:=true;
    for eEXT in EXT
    do
      if IsFirst=false then
        AppendTo(output, ",");
      fi;
      IsFirst:=false;
      PrintLine(eEXT);
    od;
    AppendTo(output, "]\n");
  od;
  AppendTo(output, "]\n");
  CloseStream(output);
  #
  TheCommand:=Concatenation(FileMinkSum, " < ", FileInp, " > ", FileOut, " 2> ", FileLog);
#  Print("Running minkSum\n");
  Exec(TheCommand);
  #
  TheCommand:=Concatenation(FileNudifyMink, " ", FileOut, " > ", FileExt);
  Exec(TheCommand);
  #
  TheReply:=ReadAsFunction(FileExt)();
#  Print("|TheReply|=", Length(TheReply), "\n");
  RemoveFile(FileInp);
  RemoveFile(FileOut);
  RemoveFile(FileLog);
  RemoveFile(FileExt);
  return TheReply;
end;

MINKSum_Direct_noredund:=function(ListEXT)
  local n, eMultiple, ListSums, eRec, eSum, eVect;
  n:=Length(ListEXT[1][1]);
  eMultiple:=BuildSetMultiple(ListEXT);
  ListSums:=[];
  for eRec in eMultiple
  do
    eSum:=ListWithIdenticalEntries(n,0);
    for eVect in eRec
    do
      eSum:=eSum+eVect;
    od;
    Add(ListSums, eSum);
  od;
  return ListSums;
end;

MINKSum_Direct:=function(ListEXT)
  return RemoveRedundancy(MINKSum_Direct_noredund(ListEXT));
end;

MINKSum_DirectEquivariant:=function(ListEXT, GRPmatr)
  local ListSums, ListPermGens, eGen, eList, GRPperm, BoundingSet, eRec;
  ListSums:=MINKSum_Direct_noredund(ListEXT);
  ListPermGens:=[];
  for eGen in GeneratorsOfGroup(GRPmatr)
  do
    eList:=List(ListSums, x->Position(ListSums, x*eGen));
    Add(ListPermGens, PermList(eList));
  od;
  GRPperm:=PersoGroupPerm(ListPermGens);
  Print("|GRPperm|=", Order(GRPperm), "\n");
  BoundingSet:=[];
  eRec:=EliminationByRedundancyEquivariant(ListSums, BoundingSet, GRPperm);
  return ListSums{eRec.eSetSelect};
end;


MINKSum_Generic:=function(ListEXT)
  return MINKSum_Direct(ListEXT);
end;


ZONOTOP_GetVerticesMinkSum:=function(ListVect)
  local ListEXT, eVect;
  ListEXT:=[];
  for eVect in ListVect
  do
    Add(ListEXT, [eVect, -eVect]);
  od;
  return MINKSum_ByWeibelFukuda(ListEXT);
end;
