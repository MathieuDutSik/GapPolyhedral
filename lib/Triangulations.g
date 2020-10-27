ExtractTriangulation:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"ExtractTriangulation");
ExtractTriangulationFacet:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"ExtractTriangulationFacet");
ExtractTopcomResults:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"ExtractTopcomResult");
TopComPoints2triang:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"points2triangs");


__RandomPositiveDefiniteMatrix:=function(n)
  local TheMat, TheInt, i, j, alpha;
  TheMat:=NullMat(n,n);
  TheInt:=2;
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      alpha:=Random([-TheInt..TheInt]);
      TheMat[i][j]:=alpha;
      TheMat[j][i]:=alpha;
    od;
  od;
  for i in [1..n]
  do
    alpha:=Random([-TheInt..TheInt]);
    TheMat[i][i]:=alpha;
  od;
  while(true)
  do
    if IsPositiveDefiniteSymmetricMatrix(TheMat) then
      return TheMat;
    fi;
    TheMat:=TheMat+IdentityMat(n);
  od;
end;


OutputToTopcom:=function(FileName, EXT, GroupExt)
  local output, i, j, EXTN, g, eMat, eList, n, eGen, eP;
  n:=Length(EXT[1]);
  eP:=[n];
  Append(eP, [1..n-1]);
  g:=PermList(eP);
  output:=OutputTextFile(FileName, true);
  EXTN:=List(EXT, x->Permuted(x, g));
  AppendTo(output, EXTN);
  AppendTo(output, "\n");
  eMat:=[];
  for eGen in GeneratorsOfGroup(GroupExt)
  do
    eList:=[];
    for i in [0..Length(EXT)-1]
    do
      j:=OnPoints(i+1, eGen)-1;
      Add(eList, j);
    od;
    Add(eMat, eList);
  od;
  AppendTo(output, eMat);
  CloseStream(output);
end;


GetAllTriangulationsEquivariant:=function(EXT, GRP)
  local FileIn, FileOut, FileErr, FileRes, TheCommand, TheResult, NewListTrig, eTrig, NewTrig;
  FileIn:=Filename(POLYHEDRAL_tmpdir,"Topcom.input");
  FileErr:=Filename(POLYHEDRAL_tmpdir,"Topcom.err");
  FileOut:=Filename(POLYHEDRAL_tmpdir,"Topcom.out");
  FileRes:=Filename(POLYHEDRAL_tmpdir,"Topcom.result");
  RemoveFileIfExist(FileIn);
  RemoveFileIfExist(FileOut);
  RemoveFileIfExist(FileRes);
  #
  OutputToTopcom(FileIn, EXT, GRP);
  TheCommand:=Concatenation(TopComPoints2triang, " < ", FileIn, " > ", FileOut, " 2> ", FileErr);
  Exec(TheCommand);
  TheCommand:=Concatenation(ExtractTopcomResults, " ", FileOut, " ", FileRes);
  Exec(TheCommand);
  #
  TheResult:=ReadAsFunction(FileRes)();
  NewListTrig:=[];
  for eTrig in TheResult
  do
    NewTrig:=List(eTrig, x->List(x, y->y+1));
    Add(NewListTrig, Set(NewTrig));
  od;
  RemoveFileIfExist(FileIn);
  RemoveFileIfExist(FileOut);
  RemoveFileIfExist(FileRes);
  return NewListTrig;
end;


GetAllTriangulations:=function(EXT)
  local GRP, ListTrig_Equiv, ListTrig_Total, eListTrig, O;
  GRP:=LinPolytope_Automorphism(EXT);
  ListTrig_Equiv:=GetAllTriangulationsEquivariant(EXT, GRP);
  ListTrig_Total:=[];
  for eListTrig in ListTrig_Equiv
  do
    O:=Orbit(GRP, eListTrig, OnSetsSets);
    Append(ListTrig_Total, O);
  od;
  return ListTrig_Total;
end;




IsTriangulationInvariant:=function(ListTrig, GRP)
  local ListSets, eGen;
  ListSets:=List(ListTrig, Set);
  for eGen in GeneratorsOfGroup(GRP)
  do
    if First(ListSets, x->Position(ListSets, OnSets(x,eGen))=fail)<>fail then
      return false;
    fi;
  od;
  return true;
end;

GetVolumesOfTriangulation:=function(EXT, ListTrig)
  return List(ListTrig, x->AbsInt(DeterminantMat(EXT{x})));
end;


TriangulationRecursiveDelaunay:=function(EXT)
  local RNK, ListUnfinished, ListTrigs, n, TmpDir, NewListUnfinished, TheGramMat, eUnfinish, TotalListVertices, eVert, eVertRed, HeightVert, FAC, eFAC, RelevantFAC, eIneq, eSet;
  RNK:=RankMat(EXT);
  if RNK<>Length(EXT[1]) then
    Error("The polytope should be full dimensional");
  fi;
  if RNK=Length(EXT) then
    return [[1..Length(EXT)]];
  fi;
  ListUnfinished:=[  [1..Length(EXT)]  ];
  ListTrigs:=[];
  n:=Length(EXT[1])-1;
  TmpDir:=Filename(POLYHEDRAL_tmpdir, "");
  while(true)
  do
    NewListUnfinished:=[];
    TheGramMat:=__RandomPositiveDefiniteMatrix(n);
    for eUnfinish in ListUnfinished
    do
      TotalListVertices:=[];
      for eVert in EXT{eUnfinish}
      do
        eVertRed:=eVert{[2..n+1]};
        HeightVert:=eVertRed*TheGramMat*eVertRed;
        Add(TotalListVertices, Concatenation(eVert, [HeightVert]));
      od;
      if RankMat(TotalListVertices) < n+2 then
        Add(NewListUnfinished, eUnfinish);
      else
        FAC:=DualDescription(TotalListVertices);
        for eIneq in FAC
        do
          if eIneq[n+2]>0 then
            eSet:=Filtered([1..Length(TotalListVertices)], x->eIneq*TotalListVertices[x]=0);
            RelevantFAC:=eUnfinish{eSet};
            if Length(RelevantFAC)=n+1 then
              Add(ListTrigs, RelevantFAC);
            else
              Add(NewListUnfinished, RelevantFAC);
            fi;
          fi;
        od;
      fi;
    od;
    if Length(NewListUnfinished)=0 then
#      Print("|Trig|=", Length(ListTrigs), "\n");
      return ListTrigs;
    fi;
    ListUnfinished:=ShallowCopy(NewListUnfinished);
#    Print("|Trig|=", Length(ListTrigs), " |Remain|=", Length(ListUnfinished), "\n");
  od;
end;


GetTriangulationFromLRS:=function(EXT)
  local FileExt, FileTriangulation, output, TheTrig;
  FileExt:=Filename(POLYHEDRAL_tmpdir,"Project.ext");
  FileTriangulation:=Filename(POLYHEDRAL_tmpdir,"Project.triangulation");
  output:=OutputTextFile(FileExt, true);;
  AppendTo(output, "V-representation\n");
  AppendTo(output, "begin\n");
  AppendTo(output, Length(EXT), " ", Length(EXT[1]), " integer\n");
  WriteMatrix(output, EXT);
  AppendTo(output, "end\n");
  AppendTo(output, "printcobasis 1\n");
  CloseStream(output);
  Exec(FileGLRS, " ", FileExt, " | ", ExtractTriangulation, " > ", FileTriangulation);
  TheTrig:=ReadAsFunction(FileTriangulation)();
  RemoveFile(FileExt);
  RemoveFile(FileTriangulation);
  return TheTrig;
end;

GetFacetsAndTriangulationFromLRS:=function(EXT)
  local FileExt, FileTriangulation, FileFacet, FileMeta, output, TheTrig, ListFacets;
  FileExt:=Filename(POLYHEDRAL_tmpdir,"Project.ext");
  FileTriangulation:=Filename(POLYHEDRAL_tmpdir,"Project.triangulation");
  FileFacet:=Filename(POLYHEDRAL_tmpdir,"Project.facet");
  FileMeta:=Filename(POLYHEDRAL_tmpdir,"Project.meta");
  output:=OutputTextFile(FileExt, true);;
  AppendTo(output, "V-representation\n");
  AppendTo(output, "begin\n");
  AppendTo(output, Length(EXT), " ", Length(EXT[1]), " integer\n");
  WriteMatrix(output, EXT);
  AppendTo(output, "end\n");
  AppendTo(output, "printcobasis 1\n");
  CloseStream(output);
  Exec(FileGLRS, " ", FileExt, " | ", ExtractTriangulationFacet, " ", FileTriangulation, " ", FileFacet, " ", FileMeta);
  TheTrig:=ReadAsFunction(FileTriangulation)();
  ListFacets:=ReadVectorFile(FileFacet);
  RemoveFile(FileExt);
  RemoveFile(FileTriangulation);
  RemoveFile(FileFacet);
  RemoveFile(FileMeta);
  return rec(TheTrig:=TheTrig, ListFacets:=Set(ListFacets));
end;

GetFacetsAndTriangulationFromLRS_Reduction:=function(EXT, GroupEXT)
  local FileExt, FileTriangulation, FileFacet, FileMeta, FileGroup, FileSupport, FileScratch, FileOutput, FileError, output, ListTrig, ListInc;
  FileExt:=Filename(POLYHEDRAL_tmpdir,"Project.ext");
  FileTriangulation:=Filename(POLYHEDRAL_tmpdir,"Project.triangulation");
  FileFacet:=Filename(POLYHEDRAL_tmpdir,"Project.facet");
  FileMeta:=Filename(POLYHEDRAL_tmpdir,"Project.meta");
  FileGroup:=Filename(POLYHEDRAL_tmpdir,"Project.group");
  FileSupport:=Filename(POLYHEDRAL_tmpdir,"Project.support");
  FileScratch:=Filename(POLYHEDRAL_tmpdir,"Project.scratch");
  FileOutput:=Filename(POLYHEDRAL_tmpdir,"Project.output");
  FileError:=Filename(POLYHEDRAL_tmpdir,"Project.error");

  output:=OutputTextFile(FileExt, true);;
  AppendTo(output, "V-representation\n");
  AppendTo(output, "begin\n");
  AppendTo(output, Length(EXT), " ", Length(EXT[1]), " integer\n");
  WriteMatrix(output, EXT);
  AppendTo(output, "end\n");
  AppendTo(output, "printcobasis 1\n");
  CloseStream(output);
  Exec(FileGLRS, " ", FileExt, " | ", ExtractTriangulationFacet, " ", FileTriangulation, " ", FileFacet, " ", FileMeta);
  ListTrig:=ReadAsFunction(FileTriangulation)();
  #
  OutputGroup(GroupEXT, Length(EXT), FileGroup);
  #
  output:=OutputTextFile(FileSupport, true);
  WriteMatrix(output, RemoveFractionMatrix(EXT));
  CloseStream(output);
  #
  Exec(FileIsoReduction, " ", FileFacet, " ", FileMeta, " ", FileGroup, " ", FileSupport, " ", FileScratch, " ", FileOutput, "2>", FileError);
  #
  ListInc:=ReadAsFunction(FileOutput)();
  RemoveFile(FileExt);
  RemoveFile(FileTriangulation);
  RemoveFile(FileFacet);
  RemoveFile(FileMeta);
  RemoveFile(FileGroup);
  RemoveFile(FileSupport);
  RemoveFile(FileScratch);
  RemoveFile(FileOutput);
  RemoveFile(FileError);
  return rec(ListTrig:=ListTrig, ListOrbitFacet:=ListInc);
end;

GetFacetAndVolumePolytope_Reduction:=function(EXT, GroupEXT)
  local TheVolume, TheINFO, n, eTrig, TheVolumeB, TheINFOb, eDet;
  TheINFO:=GetFacetsAndTriangulationFromLRS_Reduction(EXT, GroupEXT);
  n:=Length(EXT[1])-1;
  TheVolume:=0;
  for eTrig in TheINFO.ListTrig
  do
    TheVolume:=TheVolume+eTrig.det;
  od;
  TheINFOb:=TriangulationRecursiveDelaunay(EXT);
  TheVolumeB:=0;
  for eTrig in TheINFOb
  do
    eDet:=AbsInt(DeterminantMat(EXT{eTrig}));
    TheVolumeB:=TheVolumeB+eDet;
  od;
  if TheVolumeB<>TheVolume then
    Error("Inconsistency in volume computation");
  fi;
  TheVolume:=TheVolume/Factorial(n);
  return rec(ListOrbitFacet:=TheINFO.ListOrbitFacet, TheVolume:=TheVolume);
end;


PolytopeVolume:=function(EXT)
  local TheVolume, eSimplex, n;
  TheVolume:=0;
  n:=Length(EXT[1])-1;
  for eSimplex in GetTriangulationFromLRS(EXT)
  do
    TheVolume:=TheVolume+eSimplex.det;
  od;
  return TheVolume/Factorial(n);
end;


DirectIntegralDelaunay:=function(EXT, TheBasis)
  local nRel, EXTinBasis, eVert, IntDeg0, IntDeg1, IntDeg2, ListGramMat, ListCoef, i, j, H, eSimplex, EXTsimplex, VolSimplex, TheBarycenter, TheSum, eDiff, iMat, TheInt, TheReturnIntegral;
  nRel:=Length(TheBasis)-1;
  EXTinBasis:=List(EXT, x->SolutionMat(TheBasis, x));
  IntDeg0:=0;
  IntDeg1:=ListWithIdenticalEntries(nRel,0);
  IntDeg2:=NullMat(nRel,nRel);
  TheReturnIntegral:=NullMat(nRel+1, nRel+1);
  ListGramMat:=[];
  ListCoef:=[];
  for i in [1..nRel]
  do
    H:=NullMat(nRel,nRel);
    H[i][i]:=1;
    Add(ListGramMat, H);
    Add(ListCoef, 1);
  od;
  for i in [1..nRel-1]
  do
    for j in [i+1..nRel]
    do
      H:=NullMat(nRel,nRel);
      H[i][j]:=1;
      H[j][i]:=1;
      Add(ListGramMat, H);
      Add(ListCoef, 1/2);
    od;
  od;
  for eSimplex in TriangulationRecursiveDelaunay(EXTinBasis)
  do
    EXTsimplex:=EXTinBasis{eSimplex};
    VolSimplex:=AbsInt(DeterminantMat(EXTsimplex));
    TheBarycenter:=Sum(EXTsimplex)/(nRel+1);
    for iMat in [1..Length(ListCoef)]
    do
      TheSum:=0;
      for eVert in EXTsimplex
      do
        eDiff:=eVert{[2..nRel+1]}-TheBarycenter{[2..nRel+1]};
        TheSum:=TheSum+eDiff*ListGramMat[iMat]*eDiff;
      od;
      eDiff:=-TheBarycenter{[2..nRel+1]};
      TheInt:=eDiff*ListGramMat[iMat]*eDiff+TheSum/((nRel+1)*(nRel+2));
      IntDeg2:=IntDeg2+VolSimplex*ListCoef[iMat]*TheInt*ListGramMat[iMat];
    od;
    IntDeg0:=IntDeg0+VolSimplex;
    IntDeg1:=IntDeg1+VolSimplex*TheBarycenter{[2..nRel+1]};
  od;
  for i in [1..nRel]
  do
    for j in [1..nRel]
    do
      TheReturnIntegral[i+1][j+1]:=IntDeg2[i][j];
    od;
  od;
  for i in [1..nRel]
  do
    TheReturnIntegral[1][i+1]:=IntDeg1[i];
    TheReturnIntegral[i+1][1]:=IntDeg1[i];
  od;
  TheReturnIntegral[1][1]:=IntDeg0;
  return TheReturnIntegral/Factorial(nRel);
end;




DirectIntegralLRS:=function(EXT, TheBasis)
  local nRel, EXTinBasis, eVert, IntDeg0, IntDeg1, IntDeg2, ListGramMat, ListCoef, i, j, H, eSimplex, EXTsimplex, VolSimplex, TheBarycenter, TheSum, eDiff, iMat, TheInt, TheReturnIntegral;
  nRel:=Length(TheBasis)-1;
  EXTinBasis:=List(EXT, x->SolutionMat(TheBasis, x));
  IntDeg0:=0;
  IntDeg1:=ListWithIdenticalEntries(nRel,0);
  IntDeg2:=NullMat(nRel,nRel);
  TheReturnIntegral:=NullMat(nRel+1, nRel+1);
  ListGramMat:=[];
  ListCoef:=[];
  for i in [1..nRel]
  do
    H:=NullMat(nRel,nRel);
    H[i][i]:=1;
    Add(ListGramMat, H);
    Add(ListCoef, 1);
  od;
  for i in [1..nRel-1]
  do
    for j in [i+1..nRel]
    do
      H:=NullMat(nRel,nRel);
      H[i][j]:=1;
      H[j][i]:=1;
      Add(ListGramMat, H);
      Add(ListCoef, 1/2);
    od;
  od;
  for eSimplex in GetTriangulationFromLRS(EXTinBasis)
  do
#    EXTsimplex:=EXTinBasis{eSimplex};
    EXTsimplex:=EXTinBasis{eSimplex.LV};
#    VolSimplex:=AbsInt(DeterminantMat(EXTsimplex));
    VolSimplex:=AbsInt(eSimplex.det);
    TheBarycenter:=Sum(EXTsimplex)/(nRel+1);
    for iMat in [1..Length(ListCoef)]
    do
      TheSum:=0;
      for eVert in EXTsimplex
      do
        eDiff:=eVert{[2..nRel+1]}-TheBarycenter{[2..nRel+1]};
        TheSum:=TheSum+eDiff*ListGramMat[iMat]*eDiff;
      od;
      eDiff:=-TheBarycenter{[2..nRel+1]};
      TheInt:=eDiff*ListGramMat[iMat]*eDiff+TheSum/((nRel+1)*(nRel+2));
      IntDeg2:=IntDeg2+VolSimplex*ListCoef[iMat]*TheInt*ListGramMat[iMat];
    od;
    IntDeg0:=IntDeg0+VolSimplex;
    IntDeg1:=IntDeg1+VolSimplex*TheBarycenter{[2..nRel+1]};
  od;
  for i in [1..nRel]
  do
    for j in [1..nRel]
    do
      TheReturnIntegral[i+1][j+1]:=IntDeg2[i][j];
    od;
  od;
  for i in [1..nRel]
  do
    TheReturnIntegral[1][i+1]:=IntDeg1[i];
    TheReturnIntegral[i+1][1]:=IntDeg1[i];
  od;
  TheReturnIntegral[1][1]:=IntDeg0;
  return TheReturnIntegral/Factorial(nRel);
end;



DirectIntegral:=function(EXT, TheBasis)
  local INT1, INT2, DoDebug;
  DoDebug:=false;
  if DoDebug=true then
    INT1:=DirectIntegralLRS(EXT, TheBasis);
    INT2:=DirectIntegralDelaunay(EXT, TheBasis);
    if INT1<>INT2 then
      Error("We have an inconsistency in integral computation");
    fi;
    return INT2;
  else
    return DirectIntegralLRS(EXT, TheBasis);
  fi;
end;


