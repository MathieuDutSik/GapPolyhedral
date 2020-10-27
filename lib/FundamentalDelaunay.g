FileNullspaceMat:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"NullspaceMat.prog");

FindDelaunayPolytope_Rational:=function(GramMat)
  local GramMatInt, n, ListCosetRed, ListCosetDiff, ListRelevantPoints, i, V, DefiningInequality, TheRandomDirection, TheLP, eVect, TheNorm, TheCVP, ListInequalities, eEnt, RetEXT;
  Print("Beginning of FindDelaunayPolytope\n");
  GramMatInt:=RemoveFractionMatrix(GramMat);
  n:=Length(GramMat);
  ListRelevantPoints:=[];
  for i in [1..n]
  do
    V:=ListWithIdenticalEntries(n,0);
    V[i]:=1;
    Add(ListRelevantPoints, ShallowCopy(V));
    V[i]:=-1;
    Add(ListRelevantPoints, ShallowCopy(V));
  od;
  DefiningInequality:=function(eVect)
    return Concatenation([eVect*GramMatInt*eVect/2], -eVect*GramMatInt);
  end;
  TheRandomDirection:=FuncRandomDirection(n, 10);
  while(true)
  do
    ListInequalities:=List(ListRelevantPoints, DefiningInequality);
    TheLP:=LinearProgramming_Rational(ListInequalities, TheRandomDirection);
    eVect:=ListWithIdenticalEntries(n,0);
    for eEnt in TheLP.primal_solution
    do
      eVect[eEnt[1]]:=eEnt[2];
    od;
    TheNorm:=eVect*GramMatInt*eVect;
    Print("TheNorm=", TheNorm, "\n");
    TheCVP:=CVPVallentinProgram_Rational(GramMatInt, eVect);
    if TheCVP.TheNorm=TheNorm then
      RetEXT:=List(TheCVP.ListVect, x->Concatenation([1], x));
      Print("Ending of FindDelaunayPolytope |RetEXT|=", Length(RetEXT), "\n");
      return RetEXT;
    fi;
    if TheNorm < TheCVP.TheNorm then
      Error("Inconsistency in norm computation");
    fi;
    for eVect in TheCVP.ListVect
    do
      Add(ListRelevantPoints, eVect);
    od;
    Print("|ListRelevantPoints|=", Length(ListRelevantPoints), "\n");
  od;
end;




FindDelaunayPolytope_QN:=function(Nval, GramMat)
  local n, ListCosetRed, ListCosetDiff, ListRelevantPoints, i, V, DefiningInequality, TheRandomDirection, TheLP, eVect, TheNorm, TheCVP, ListInequalities, eEnt, RetEXT;
  Print("Beginning of FindDelaunayPolytope_QN\n");
  n:=Length(GramMat);
  ListRelevantPoints:=[];
  for i in [1..n]
  do
    V:=ListWithIdenticalEntries(n,0);
    V[i]:=1;
    Add(ListRelevantPoints, ShallowCopy(V));
    V[i]:=-1;
    Add(ListRelevantPoints, ShallowCopy(V));
  od;
  DefiningInequality:=function(eVect)
    return Concatenation([eVect*GramMat*eVect/2], -eVect*GramMat);
  end;
  TheRandomDirection:=FuncRandomDirection(n, 10);
  while(true)
  do
    ListInequalities:=List(ListRelevantPoints, DefiningInequality);
    TheLP:=LinearProgramming_QN(Nval, ListInequalities, TheRandomDirection);
    eVect:=ListWithIdenticalEntries(n,0);
    for eEnt in TheLP.primal_solution
    do
      eVect[eEnt[1]]:=eEnt[2];
    od;
    TheNorm:=eVect*GramMat*eVect;
#    Print("TheNorm=", TheNorm, "\n");
    TheCVP:=CVPVallentinProgram_QN(Nval, GramMat, eVect);
    if TheCVP.TheNorm=TheNorm then
      RetEXT:=List(TheCVP.ListVect, x->Concatenation([1], x));
      Print("Ending of FindDelaunayPolytope_QN |RetEXT|=", Length(RetEXT), "\n");
      return RetEXT;
    fi;
    if QN_IsPositive(Nval, TheNorm-TheCVP.TheNorm)=false then
      Error("Inconsistency in norm computation");
    fi;
    for eVect in TheCVP.ListVect
    do
      Add(ListRelevantPoints, eVect);
    od;
    Print("|ListRelevantPoints|=", Length(ListRelevantPoints), "\n");
  od;
end;

FindDelaunayPolytope:=function(GramMat)
  local Nval;
  if IsMatrixRational(GramMat)=true then
    return FindDelaunayPolytope_Rational(GramMat);
  fi;
  for Nval in [2,5]
  do
    if QN_IsMatrix(Nval, GramMat)=true then
      return FindDelaunayPolytope_QN(Nval, GramMat);
    fi;
  od;
  Error("You have to build your own arithmetic");
end;




CenterRadiusDelaunayPolytopeGeneral_Kernel:=function(GramMat, EXT)
  local ListEquation, ListB, n, iV, eV, fV, Sum, i, j, Equa, Solu, w, eCent, ListRadius, eLine, eW, eEXT;
  n:=Length(GramMat);
  ListEquation:=[];
  ListB:=[];
  for iV in [2..Length(EXT)]
  do
    eV:=EXT[1]{[2..n+1]};
    fV:=EXT[iV]{[2..n+1]};
    Sum:=eV*GramMat*eV-fV*GramMat*fV;
    Add(ListB, Sum);
    Equa:=[];
    for i in [1..n]
    do
      Sum:=0;
      for j in [1..n]
      do
        Sum:=Sum+GramMat[i][j]*(eV[j]-fV[j]);
      od;
      Add(Equa, 2*Sum);
    od;
    Add(ListEquation, Equa);
  od;
  for eLine in NullspaceMat(TransposedMat(EXT))
  do
    Add(ListB, eLine[1]);
    Add(ListEquation, -eLine{[2..n+1]});
  od;
  Solu:=SolutionMat(TransposedMat(ListEquation), ListB);
  if Solu=fail then
    return fail;
  fi;
  eCent:=Concatenation([1], Solu);
  ListRadius:=[];
  for eEXT in EXT
  do
    eW:=Solu-eEXT{[2..n+1]};
    Add(ListRadius, eW*GramMat*eW);
  od;
  if Length(Set(ListRadius))<>1 then
    Error("Center Delaunay: found incoherent distances");
  fi;
  return rec(Center:=eCent, SquareRadius:=ListRadius[1]);
end;


CenterRadiusDelaunayPolytopeGeneral:=function(GramMat, EXT)
  local TheRes;
  TheRes:=CenterRadiusDelaunayPolytopeGeneral_Kernel(GramMat, EXT);
  if TheRes=fail then
    Print("The Delaunay does not admit any circumscribing sphere\n");
    Error("Please correct");
  fi;
  return TheRes;
end;


#
#
# GramMat is a n x n Gram Matrix
# Delaunay is the list of vertices of the Delaunay expressed
# as list of integers (with 1 in first place, so of length n+1).
# Facet is a facet of the Delaunay, expressed as an incidence list
# 
# We use a Graver basis from the standard basis of Z^n.
# It is hard to see how to do any better in a systematic way.
FindAdjacentDelaunayPolytope:=function(GramMat, EXT, ListInc)
  local iVert, eVert, IndependentBasis, CP, MinRadius, SelectedVertex, reply, i, n, ListGraverOptions, GetCenterRadius, IsImprovement, NewTestVert, TheRadius, TheFac, iCol, eVect;
  n:=Length(GramMat);
  IndependentBasis:=RowReduction(EXT{ListInc}, n).EXT;
  TheFac:=__FindFacetInequality(EXT, ListInc);
  iCol:=First([2..n+1], x->TheFac[x]<>0);
  eVect:=ListWithIdenticalEntries(n+1, 0);
  eVect[iCol]:=-SignInt(TheFac[iCol]);
  SelectedVertex:=EXT[ListInc[1]]+eVect;
  GetCenterRadius:=function(TheVert)
    local VSet;
    VSet:=Concatenation(IndependentBasis, [TheVert]);
    return CenterRadiusDelaunayPolytopeGeneral(GramMat, VSet);
  end;
  MinRadius:=GetCenterRadius(SelectedVertex).SquareRadius;
  ListGraverOptions:=[];
  for i in [1..n]
  do
    eVect:=ListWithIdenticalEntries(n+1,0);
    eVect[i+1]:=1;
    Add(ListGraverOptions, ShallowCopy(eVect));
    eVect[i+1]:=-1;
    Add(ListGraverOptions, ShallowCopy(eVect));
  od;
  while(true)
  do
    eVect:=ListWithIdenticalEntries(n+1,0);
    IsImprovement:=false;
    for eVect in ListGraverOptions
    do
      NewTestVert:=SelectedVertex+eVect;
      if TheFac*NewTestVert < 0 then
        TheRadius:=GetCenterRadius(NewTestVert).SquareRadius;
        if TheRadius < MinRadius then
          IsImprovement:=true;
          SelectedVertex:=ShallowCopy(NewTestVert);
          MinRadius:=TheRadius;
        fi;
      fi;
    od;
    if IsImprovement=false then
      break;
    fi;
  od;
  while(true)
  do
#    Print("Iterating in FindAdjacentDelaunayPolytope\n");
    CP:=GetCenterRadius(SelectedVertex);
    reply:=CVPVallentinProgram(GramMat, CP.Center{[2..n+1]});
    if reply.TheNorm=CP.SquareRadius then
      break;
    fi;
    SelectedVertex:=Concatenation([1], reply.ListVect[1]);
  od;
  return List(reply.ListVect, x->Concatenation([1], x));
end;


oldFunctions_FindAdjacentDelaunayPolytope:=function(GramMat, EXT, ListInc)
  local iVert, eVert, IndependentBasis, VSet, fVert, CP, MinRadius, SelectedVertex, Vcent, reply, i, n;
  n:=Length(GramMat);
  IndependentBasis:=RowReduction(EXT{ListInc}, n).EXT;
  MinRadius:=0;
  SelectedVertex:=0;
  for iVert in Difference([1..Length(EXT)], ListInc)
  do
    eVert:=EXT[iVert];
    fVert:=IndependentBasis[1]+IndependentBasis[2]-eVert;
    VSet:=Concatenation(IndependentBasis, [fVert]);
    CP:=CenterRadiusDelaunayPolytopeGeneral(GramMat, VSet);
    if MinRadius=0 or CP.SquareRadius < MinRadius then
      MinRadius:=CP.SquareRadius;
      SelectedVertex:=fVert;
    fi;
  od;
  while(true)
  do
    VSet:=Concatenation(IndependentBasis, [SelectedVertex]);
    CP:=CenterRadiusDelaunayPolytopeGeneral(GramMat, VSet);
    Vcent:=CP.Center{[2..n+1]};
    reply:=CVPVallentinProgram(GramMat, Vcent);
    if reply.TheNorm=CP.SquareRadius then
      break;
    else
      SelectedVertex:=[1];
      Append(SelectedVertex, reply.ListVect[1]);
    fi;
  od;
  return List(reply.ListVect, x->Concatenation([1], x));
end;




VoronoiLinearInequality:=function(ExtractedBasis, TheVert, TheBasis)
  local TheVectRed, B, TheIneq, MAT, n, TheSum, k, eVect;
  n:=Length(TheBasis[1]);
  TheVectRed:=TheVert{[2..n+1]};
  B:=SolutionMat(ExtractedBasis, TheVert);
  TheIneq:=[];
  for MAT in TheBasis
  do
    TheSum:=TheVectRed*MAT*TheVectRed;
    for k in [1..n+1]
    do
      eVect:=ExtractedBasis[k]{[2..n+1]};  
      TheSum:=TheSum-B[k]*(eVect*MAT*eVect);
    od;
    Add(TheIneq, TheSum);
  od;
  return TheIneq;
end;



ListEqualitiesDelaunay:=function(EXT, TheBasis)
  local ExtractedBasis;
  ExtractedBasis:=RowReduction(EXT, Length(EXT[1])).EXT;
  return List(EXT, x->VoronoiLinearInequality(ExtractedBasis, x, TheBasis));
end;









FormsByDelaunay:=function(EXT)
  local n, BasisPSDn, ListEqualities, ListSolu, SpaceBasis, eSol, iCol, TheMat;
  n:=Length(EXT[1])-1;
  BasisPSDn:=InvariantFormDutourVersion([IdentityMat(n)]);
  ListEqualities:=ListEqualitiesDelaunay(EXT, BasisPSDn);
  ListSolu:=NullspaceMat(TransposedMat(ListEqualities));
  SpaceBasis:=[];
  for eSol in ListSolu
  do
    TheMat:=NullMat(n, n);
    for iCol in [2..Length(eSol[1])]
    do
      TheMat:=TheMat+eSol[iCol]*BasisPSDn[iCol-1];
    od;
    Add(SpaceBasis, RemoveFractionMatrix(TheMat));
  od;
  return SpaceBasis;
end;





#
# actually we put a transposed here
GetTransposeNullspaceMat:=function(EXT)
  local TheDim, FileInput, FileOutput, output, TheRead, ListMat;
  TheDim:=Length(EXT[1]);
  FileInput:=Filename(POLYHEDRAL_tmpdir,"NullSpa.input");
  FileOutput:=Filename(POLYHEDRAL_tmpdir,"NullSpa.output");
  RemoveFileIfExist(FileInput);
  RemoveFileIfExist(FileOutput);
  TheDim:=Length(EXT[1]);
  output:=OutputTextFile(FileInput, true);
  AppendTo(output, TheDim, "\n");
  AppendTo(output, Length(EXT), "\n");
  WriteMatrix(output, EXT);
  CloseStream(output);
  #
  Exec(FileNullspaceMat, " ", FileInput, " ", FileOutput);
  TheRead:=ReadAsFunction(FileOutput)();
  RemoveFile(FileInput);
  RemoveFile(FileOutput);
  return TheRead;
end;


#
#
# Get the nullspace, i.e. the family of matrices M
# such that v M v=0 for all v in EXT
# it uses C++ and gmp for higher speed.
# ComputeRankPolytope
GetRankBasisPolytope:=function(EXT)
  local TheSpace, ListMat, eVector, EXTinp, eEXT, eMat, i, TheDim;
  TheDim:=Length(EXT[1]);
  EXTinp:=[];
  for eEXT in EXT
  do
    eMat:=TransposedMat([eEXT])*[eEXT];
    Add(EXTinp, SymmetricMatrixToVector(eMat));
  od;
  TheSpace:=GetTransposeNullspaceMat(EXTinp);
  ListMat:=[];
  for eVector in TheSpace
  do
    eMat:=VectorToSymmetricMatrix(eVector, TheDim);
    for i in [1..TheDim]
    do
      eMat[i][i]:=2*eMat[i][i];
    od;
    Add(ListMat, RemoveFractionMatrix(eMat));
  od;
  return ListMat;
end;








IsGeneratingDelaunayPolytope:=function(EXT)
  local OneBase;
  OneBase:=BaseIntMat(EXT);
  return AbsInt(DeterminantMat(OneBase))=1;
end;



DistanceMatrixDelaunay:=function(GramMatrix, EXT)
  local hDim, DistMat, NbV, EXTred, iVertex, jVertex, Vvector, dist;
  hDim:=Length(EXT[1]);
  NbV:=Length(EXT);
  EXTred:=List(EXT, x->x{[2..hDim]});
  DistMat:=NullMat(NbV, NbV);
  for iVertex in [1..NbV-1]
  do
    for jVertex in [iVertex+1..NbV]
    do
      Vvector:=EXTred[jVertex]-EXTred[iVertex];
      dist:=Vvector*GramMatrix*Vvector;
      DistMat[iVertex][jVertex]:=dist;
      DistMat[jVertex][iVertex]:=dist;
    od;
  od;
  return DistMat;
end;



DistanceMatrixExtremeDelaunay:=function(EXT)
  local n, GetValueVector, ListVect, NSP, TheMat, TheMatRed, nbVert, DistanceMatrix, iVert, jVert, eDiff, eDist, i;
  n:=Length(EXT[1])-1;
  GetValueVector:=function(eVect)
    local fVect;
    fVect:=Concatenation([1], eVect{[2..n+1]});
    return SymmetricMatrixToVector(TransposedMat([fVect])*[fVect]);
  end;
  ListVect:=List(EXT, x->GetValueVector(x));
  NSP:=NullspaceMat(TransposedMat(ListVect));
  if Length(NSP)>1 then
    Error("We have a problem somewhere");
  fi;
  TheMat:=VectorToSymmetricMatrix(NSP[1], n+1);
  TheMatRed:=List(TheMat{[2..n+1]}, x->x{[2..n+1]});
  for i in [1..n]
  do
    TheMatRed[i][i]:=TheMatRed[i][i]*2;
  od;
  return RemoveFractionMatrix(DistanceMatrixDelaunay(TheMatRed, EXT));
end;










#
# The condition below if satisfied and if the polytope
# is extreme ensures that the covering density achieves
# a maximum there.
TestDelaunayEutacticityCondition:=function(EXT, GramMat)
  local n, CP, eCentRed, ListDiff, ListMat, TheMat, ListEquations, nbVert, H, iVert, i, j, NSP, TheLP, ListInequalities, ToBeMinimized, eVect, eEnt, TheSol, TheSolRed, TheSumVect, TheSumMat, iCol, TheSol2;
  n:=Length(EXT[1])-1;
  CP:=CenterRadiusDelaunayPolytopeGeneral(GramMat, EXT);
  eCentRed:=CP.Center{[2..n+1]};
  ListDiff:=List(EXT, x->x{[2..n+1]}-eCentRed);
  ListMat:=List(ListDiff, x->TransposedMat([x])*[x]);
  TheMat:=(CP.SquareRadius/n)*Inverse(GramMat);
  ListEquations:=[];
  nbVert:=Length(EXT);
  H:=ListWithIdenticalEntries(1+nbVert, 0);
  H[1]:=1;
  for iVert in [1..nbVert]
  do
    H[iVert+1]:=-1;
  od;
  Add(ListEquations, ShallowCopy(H));
  for i in [1..n]
  do
    H:=ListWithIdenticalEntries(1+nbVert, 0);
    for iVert in [1..nbVert]
    do
      H[iVert+1]:=ListDiff[iVert][i];
    od;
    Add(ListEquations, ShallowCopy(H));
  od;
  for i in [1..n]
  do
    for j in [i..n]
    do
      H:=ListWithIdenticalEntries(1+nbVert, 0);
      H[1]:=TheMat[i][j];
      for iVert in [1..nbVert]
      do
        H[iVert+1]:=-ListMat[iVert][i][j];
      od;
      Add(ListEquations, ShallowCopy(H));
    od;
  od;
  NSP:=NullspaceMat(TransposedMat(ListEquations));
  Print("|Equa|=", Length(ListEquations), "  |LinSpa|=", Length(NSP), "\n");
  ListInequalities:=[];
  for iVert in [1..nbVert]
  do
    H:=ListWithIdenticalEntries(1+Length(NSP), 0);
    H[1]:=-1;
    for iCol in [1..Length(NSP)]
    do
      H[iCol+1]:=NSP[iCol][iVert+1];
    od;
    Add(ListInequalities, ShallowCopy(H));
  od;
  ToBeMinimized:=ListWithIdenticalEntries(1+Length(NSP), 0);
  for iCol in [1..Length(NSP)]
  do
    ToBeMinimized[iCol+1]:=NSP[iCol][1];
  od;
  TheLP:=LinearProgramming(ListInequalities, ToBeMinimized);
  if IsBound(TheLP.primal_solution) then
    eVect:=ListWithIdenticalEntries(Length(NSP),0);
    for eEnt in TheLP.primal_solution
    do
      eVect[eEnt[1]]:=eEnt[2];
    od;
    TheSol:=eVect*NSP;
    TheSol2:=TheSol/TheSol[1];
    TheSolRed:=TheSol2{[2..nbVert+1]};
    for iVert in [1..nbVert]
    do
      if TheSolRed[iVert]<=0 then
        Error("We have a failure of positivity, please debug");
      fi;
    od;
    TheSumVect:=TheSolRed*ListDiff;
    TheSumMat:=TheSolRed*ListMat;
    if Sum(TheSolRed)<>1 then
      Error("There is incoherence in sum of coefficients");
    fi;
    if TheSumVect<>ListWithIdenticalEntries(n, 0) then
      Error("There is incoherence in sum vect");
    fi;
    if TheSumMat<>TheMat then
      Error("There is incoherence in sum mat");
    fi;
    return TheSolRed;
  else
    return false;
  fi;
end;


TestDelaunayEutacticityConditionPartitioned:=function(EXT, ThePartition, GramMat)
  local n, CP, eCentRed, ListDiff, ListMat, TheMat, ListEquations, nbVert, H, iVert, i, j, NSP, TheLP, ListInequalities, ToBeMinimized, eVect, eEnt, TheSol, TheSolRed, TheSumVect, TheSumMat, iCol, TheSol2, TheSolRedByPart, ListDiffByPart, ListMatByPart, iPart;
  n:=Length(EXT[1])-1;
  CP:=CenterRadiusDelaunayPolytopeGeneral(GramMat, EXT);
  eCentRed:=CP.Center{[2..n+1]};
  ListDiff:=List(EXT, x->x{[2..n+1]}-eCentRed);
  ListMat:=List(ListDiff, x->TransposedMat([x])*[x]);
  ListDiffByPart:=List(ThePartition, x->Sum(ListDiff{x}));
  ListMatByPart:=List(ThePartition, x->Sum(ListMat{x}));
  TheMat:=(CP.SquareRadius/n)*Inverse(GramMat);
  ListEquations:=[];
  nbVert:=Length(EXT);
  H:=ListWithIdenticalEntries(1+Length(ThePartition), 0);
  H[1]:=1;
  for iPart in [1..Length(ThePartition)]
  do
    H[iPart+1]:=-Length(ThePartition[iPart]);
  od;
  Add(ListEquations, ShallowCopy(H));
  for i in [1..n]
  do
    H:=ListWithIdenticalEntries(1+Length(ThePartition), 0);
    for iPart in [1..Length(ThePartition)]
    do
      H[iPart+1]:=ListDiffByPart[iPart][i];
    od;
    Add(ListEquations, ShallowCopy(H));
  od;
  for i in [1..n]
  do
    for j in [i..n]
    do
      H:=ListWithIdenticalEntries(1+Length(ThePartition), 0);
      H[1]:=TheMat[i][j];
      for iPart in [1..Length(ThePartition)]
      do
        H[iPart+1]:=-ListMatByPart[iPart][i][j];
      od;
      Add(ListEquations, ShallowCopy(H));
    od;
  od;
  NSP:=NullspaceMat(TransposedMat(ListEquations));
#  Print("|Equa|=", Length(ListEquations), "  |LinSpa|=", Length(NSP), "\n");
#  Print("|ThePartition|=", List(ThePartition, Length), "\n");
  ListInequalities:=[];
  for iPart in [1..Length(ThePartition)]
  do
    H:=ListWithIdenticalEntries(1+Length(NSP), 0);
    H[1]:=-1;
    for iCol in [1..Length(NSP)]
    do
      H[iCol+1]:=NSP[iCol][iPart+1];
    od;
    Add(ListInequalities, ShallowCopy(H));
  od;
  ToBeMinimized:=ListWithIdenticalEntries(1+Length(NSP), 0);
  for iCol in [1..Length(NSP)]
  do
    ToBeMinimized[iCol+1]:=NSP[iCol][1];
  od;
  TheLP:=LinearProgramming(ListInequalities, ToBeMinimized);
  if IsBound(TheLP.primal_solution) then
    eVect:=ListWithIdenticalEntries(Length(NSP),0);
    for eEnt in TheLP.primal_solution
    do
      eVect[eEnt[1]]:=eEnt[2];
    od;
    TheSol:=eVect*NSP;
    TheSol2:=TheSol/TheSol[1];
    TheSolRedByPart:=TheSol2{[2..Length(ThePartition)+1]};
    TheSolRed:=ListWithIdenticalEntries(nbVert, 0);
    for iPart in [1..Length(ThePartition)]
    do
      TheSolRed{ThePartition[iPart]}:=ListWithIdenticalEntries(Length(ThePartition[iPart]), TheSolRedByPart[iPart]);
    od;
    for iVert in [1..nbVert]
    do
      if TheSolRed[iVert]<=0 then
        Error("We have a failure of positivity");
      fi;
    od;
    TheSumVect:=TheSolRed*ListDiff;
    TheSumMat:=TheSolRed*ListMat;
    if Sum(TheSolRed)<>1 then
      Error("There is incoherence in sum of coefficients");
    fi;
    if TheSumVect<>ListWithIdenticalEntries(n, 0) then
      Error("There is incoherence in sum vect");
    fi;
    if TheSumMat<>TheMat then
      Error("There is incoherence in sum mat");
    fi;
    return TheSolRed;
  else
    return false;
  fi;
end;



TestDelaunayWeakEutacticityConditionPartitioned:=function(EXT, ThePartition, GramMat)
  local n, CP, eCentRed, ListDiff, ListMat, TheMat, ListEquations, nbVert, H, iVert, i, j, NSP, TheLP, ListInequalities, ToBeMinimized, eVect, eEnt, TheSol, TheSolRed, TheSumVect, TheSumMat, iCol, TheSol2, TheSolRedByPart, ListDiffByPart, ListMatByPart, iPart;
  n:=Length(EXT[1])-1;
  CP:=CenterRadiusDelaunayPolytopeGeneral(GramMat, EXT);
  eCentRed:=CP.Center{[2..n+1]};
  ListDiff:=List(EXT, x->x{[2..n+1]}-eCentRed);
  ListMat:=List(ListDiff, x->TransposedMat([x])*[x]);
  ListDiffByPart:=List(ThePartition, x->Sum(ListDiff{x}));
  ListMatByPart:=List(ThePartition, x->Sum(ListMat{x}));
  TheMat:=(CP.SquareRadius/n)*Inverse(GramMat);
  ListEquations:=[];
  nbVert:=Length(EXT);
  H:=ListWithIdenticalEntries(1+Length(ThePartition), 0);
  H[1]:=1;
  for iPart in [1..Length(ThePartition)]
  do
    H[iPart+1]:=-Length(ThePartition[iPart]);
  od;
  Add(ListEquations, ShallowCopy(H));
  for i in [1..n]
  do
    H:=ListWithIdenticalEntries(1+Length(ThePartition), 0);
    for iPart in [1..Length(ThePartition)]
    do
      H[iPart+1]:=ListDiffByPart[iPart][i];
    od;
    Add(ListEquations, ShallowCopy(H));
  od;
  for i in [1..n]
  do
    for j in [i..n]
    do
      H:=ListWithIdenticalEntries(1+Length(ThePartition), 0);
      H[1]:=TheMat[i][j];
      for iPart in [1..Length(ThePartition)]
      do
        H[iPart+1]:=-ListMatByPart[iPart][i][j];
      od;
      Add(ListEquations, ShallowCopy(H));
    od;
  od;
  NSP:=NullspaceMat(TransposedMat(ListEquations));
#  Print("|Equa|=", Length(ListEquations), "  |LinSpa|=", Length(NSP), "\n");
#  Print("|ThePartition|=", List(ThePartition, Length), "\n");
  ListInequalities:=[];
  for iPart in [1..Length(ThePartition)]
  do
    H:=ListWithIdenticalEntries(1+Length(NSP), 0);
    H[1]:=0;
    for iCol in [1..Length(NSP)]
    do
      H[iCol+1]:=NSP[iCol][iPart+1];
    od;
    Add(ListInequalities, ShallowCopy(H));
  od;
  H:=ListWithIdenticalEntries(1+Length(NSP), 0);
  H[1]:=-1;
  for iPart in [1..Length(ThePartition)]
  do
    for iCol in [1..Length(NSP)]
    do
      H[iCol+1]:=H[iCol+1]+NSP[iCol][iPart+1];
    od;
  od;
  Add(ListInequalities, ShallowCopy(H));
  ToBeMinimized:=ListWithIdenticalEntries(1+Length(NSP), 0);
  for iCol in [1..Length(NSP)]
  do
    ToBeMinimized[iCol+1]:=NSP[iCol][1];
  od;
  TheLP:=LinearProgramming(ListInequalities, ToBeMinimized);
  if IsBound(TheLP.primal_solution) then
    eVect:=ListWithIdenticalEntries(Length(NSP),0);
    for eEnt in TheLP.primal_solution
    do
      eVect[eEnt[1]]:=eEnt[2];
    od;
    TheSol:=eVect*NSP;
    TheSol2:=TheSol/TheSol[1];
    TheSolRedByPart:=TheSol2{[2..Length(ThePartition)+1]};
    TheSolRed:=ListWithIdenticalEntries(nbVert, 0);
    for iPart in [1..Length(ThePartition)]
    do
      TheSolRed{ThePartition[iPart]}:=ListWithIdenticalEntries(Length(ThePartition[iPart]), TheSolRedByPart[iPart]);
    od;
    for iVert in [1..nbVert]
    do
      if TheSolRed[iVert] < 0 then
        Error("We have a failure of positivity");
      fi;
    od;
    TheSumVect:=TheSolRed*ListDiff;
    TheSumMat:=TheSolRed*ListMat;
    if Sum(TheSolRed)<>1 then
      Error("There is incoherence in sum of coefficients");
    fi;
    if TheSumVect<>ListWithIdenticalEntries(n, 0) then
      Error("There is incoherence in sum vect");
    fi;
    if TheSumMat<>TheMat then
      Error("There is incoherence in sum mat");
    fi;
    return TheSolRed;
  else
    return false;
  fi;
end;





TestSimplexPropertyInExtreme:=function(EXT, GramMat, TheSimplex, TheTest)
  local n, GetSymMat, PsiDeltaVMatrix, CP, RightHandSideMat, ListComplement, nbVertComp, ListMat, ListEquations, i, j, H, iVert, NSP, ToBeMinimized, ListInequalities, iCol, TheSum, TheLP, eVect, eEnt, TheSol, TheSol2, TheSolRed;
  n:=Length(GramMat);
  GetSymMat:=function(eVect)
    local eVectRed;
    eVectRed:=eVect{[2..n+1]};
    return TransposedMat([eVectRed])*[eVectRed];
  end;
  PsiDeltaVMatrix:=function(TheVect)
    local H, TheSymmMat, iH;
    H:=SolutionMat(EXT{TheSimplex}, TheVect);
    TheSymmMat:=GetSymMat(TheVect);
    for iH in [1..Length(H)]
    do
      TheSymmMat:=TheSymmMat-H[iH]*GetSymMat(EXT[TheSimplex[iH]]);
    od;
    return TheSymmMat;
  end;
  if TheTest<>"relative interior" and TheTest<>"closed" then
    Print("The test should be \"relative interior\" or \"closed\"\n");
    Error("Please correct this point");
  fi;
  CP:=CenterRadiusDelaunayPolytopeGeneral(GramMat, EXT);
  RightHandSideMat:=PsiDeltaVMatrix(CP.Center)+(CP.SquareRadius/n)*Inverse(GramMat);
  ListComplement:=Difference([1..Length(EXT)], Set(TheSimplex));
  nbVertComp:=Length(ListComplement);
  ListMat:=List(ListComplement, x->PsiDeltaVMatrix(EXT[x]));
  ListEquations:=[];
  for i in [1..n]
  do
    for j in [i..n]
    do
      H:=ListWithIdenticalEntries(1+nbVertComp, 0);
      H[1]:=RightHandSideMat[i][j];
      for iVert in [1..nbVertComp]
      do
        H[1+iVert]:=-ListMat[iVert][i][j];
      od;
      Add(ListEquations, ShallowCopy(H));
    od;
  od;
  NSP:=NullspaceMat(TransposedMat(ListEquations));
  Print("|Equa|=", Length(ListEquations), "  |LinSpa|=", Length(NSP), "\n");
  ToBeMinimized:=ListWithIdenticalEntries(1+Length(NSP), 0);
  for iCol in [1..Length(NSP)]
  do
    ToBeMinimized[iCol+1]:=NSP[iCol][1];
  od;
  ListInequalities:=[];
  if TheTest="relative interior" then
    for iVert in [1..nbVertComp]
    do
      H:=ListWithIdenticalEntries(1+Length(NSP), 0);
      H[1]:=-1;
      for iCol in [1..Length(NSP)]
      do
        H[iCol+1]:=NSP[iCol][iVert+1];
      od;
      Add(ListInequalities, ShallowCopy(H));
    od;
  elif TheTest="closed" then
    for iVert in [1..nbVertComp]
    do
      H:=ListWithIdenticalEntries(1+Length(NSP), 0);
      H[1]:=0;
      for iCol in [1..Length(NSP)]
      do
        H[iCol+1]:=NSP[iCol][iVert+1];
      od;
      Add(ListInequalities, ShallowCopy(H));
    od;
    H:=ListWithIdenticalEntries(1+Length(NSP), 0);
    H[1]:=-1;
    for iCol in [1..Length(NSP)]
    do
      TheSum:=0;
      for iVert in [1..nbVertComp]
      do
        TheSum:=TheSum+NSP[iCol][iVert+1];
      od;
      H[iCol+1]:=TheSum;
    od;
    Add(ListInequalities, ShallowCopy(H));
  else
    Error("We should never reach this stage");
  fi;
  TheLP:=LinearProgramming(ListInequalities, ToBeMinimized);
  if IsBound(TheLP.primal_solution)=false  then
    return false;
  fi;
  eVect:=ListWithIdenticalEntries(Length(NSP),0);
  for eEnt in TheLP.primal_solution
  do
    eVect[eEnt[1]]:=eEnt[2];
  od;
  TheSol:=eVect*NSP;
  TheSol2:=TheSol/TheSol[1];
  TheSolRed:=TheSol2{[2..nbVertComp+1]};
  if TheSolRed*ListMat<>RightHandSideMat then
    Error("There is incoherence in sum mat");
  fi;
  if TheTest="relative interior" then
    for iVert in [1..nbVertComp]
    do
      if TheSolRed[iVert]<=0 then
        Error("We have a failure of strict positivity (>0), please debug");
      fi;
    od;
  elif TheTest="closed" then
    for iVert in [1..nbVertComp]
    do
      if TheSolRed[iVert]< 0 then
        Error("We have a failure of non-negativity (>=0), please debug");
      fi;
    od;
  fi;
  return TheSolRed;
end;





FuncExtreme:=function(EXT)
  local n, ListBasis, ListOcc, i, TheMat, j, ListBasisEqua, H, eLine, TheGram, EXTmin, EXTred, TheMatVert, B, vi, v1, W, TheCent, TheSpa, LVAL, EXTminred, GramMatrix;
  n:=Length(EXT[1])-1;
  ListBasis:=[];
  ListOcc:=[];
  for i in [1..n]
  do
    TheMat:=NullMat(n,n);
    TheMat[i][i]:=1;
    Add(ListBasis, TheMat);
    Add(ListOcc, [i,i]);
  od;
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      TheMat:=NullMat(n,n);
      TheMat[i][j]:=1;
      TheMat[j][i]:=1;
      Add(ListBasis, TheMat);
      Add(ListOcc, [i,j]);
    od;
  od;
  ListBasisEqua:=ListEqualitiesDelaunay(EXT, ListBasis);
  H:=ListWithIdenticalEntries(Length(ListBasisEqua[1]), 0);
  H[1]:=1;
  Add(ListBasisEqua, H);
  TheSpa:=NullspaceMat(TransposedMat(ListBasisEqua));
  if Length(TheSpa)<>1 then
    Print("|TheSpa|=", Length(TheSpa), "\n");
    Error("We have an error: the dimension of the space is not correct");
  fi;
  eLine:=RemoveFraction(TheSpa[1]);
  TheGram:=NullMat(n, n);
  for i in [1..Length(ListBasis)]
  do
    TheGram:=TheGram+eLine[i+1]*ListBasis[i];
  od;
  if RankMat(TheGram)=Length(TheGram) then
    if IsPositiveDefiniteSymmetricMatrix(TheGram)=false then
      GramMatrix:=RemoveFractionMatrix(-TheGram);
    else
      GramMatrix:=RemoveFractionMatrix(TheGram);
    fi;
  else
    if IsPositiveSymmetricMatrix(TheGram)=false then
      GramMatrix:=RemoveFractionMatrix(-TheGram);
    else
      GramMatrix:=RemoveFractionMatrix(TheGram);
    fi;
  fi;
  if RankMat(TheGram) < n then
    return rec(GramMatrix:=GramMatrix, TheCent:="you crazy?", RhoSquare:="Really you are");
  fi;
  EXTmin:=RowReduction(EXT).EXT;
  EXTred:=List(EXT, x->x{[2..n+1]});
  EXTminred:=List(EXTmin, x->x{[2..n+1]});
  TheMatVert:=[];
  B:=[];
  for i in [1..n]
  do
    vi:=EXTminred[i+1];
    v1:=EXTminred[1];
    Add(B, vi*GramMatrix*vi-v1*GramMatrix*v1);
    Add(TheMatVert, vi-v1);
  od;
  W:=B*Inverse(TransposedMat(TheMatVert));
  TheCent:=W*Inverse(GramMatrix)/2;
  LVAL:=List(EXTred, x->(x-TheCent)*GramMatrix*(x-TheCent));
  if Length(Set(LVAL))>1 then
    Error("We have an error: the sphere does not match");
  fi;
  return rec(GramMatrix:=GramMatrix, TheCent:=TheCent, RhoSquare:=LVAL[1]);
end;

Rational_BaseIntMat:=function(TheMat)
  local INF, TheBas;
  INF:=RemoveFractionMatrixPlusCoef(TheMat);
  TheBas:=BaseIntMat(INF.TheMat);
  return TheBas/INF.TheMult;
end;


GetPresentationGeneratingDelaunay:=function(EXT)
  local ListDiff, P;
  ListDiff:=List(EXT, x->x-EXT[1]);
  P:=Concatenation([EXT[1]], Rational_BaseIntMat(ListDiff));
  return List(EXT, x->SolutionMat(P, x));
end;

RankPolytope:=function(EXT)
  return Length(GetRankBasisPolytope(GetPresentationGeneratingDelaunay(EXT)));
end;



IsPerfectDelaunay:=function(EXT)
  local P, EXT2, INF, GramMatrix, TheCenter, reply, EXTtest;
  if RankPolytope(EXT)<>1 then
    return false;
  fi;
  EXT2:=GetPresentationGeneratingDelaunay(EXT);
  INF:=FuncExtreme(EXT2);
  reply:=CVPVallentinProgram(INF.GramMatrix, INF.TheCent);
  EXTtest:=List(reply.ListVect, x->Concatenation([1], x));
  return Set(EXT2)=Set(EXTtest);
end;


ListExtensionOfGivenDelaunay:=function(EXT, TheMod, GramMat)
  local n, eVect, CP, ListSolutionsSameRadius, ListSolutionsSameEXT, NewBasis, NewGramMat, eBigBasis, eInvBasis, EXTbig, CVP, eCenterBig, eCenterBigRed;
  n:=Length(GramMat);
  CP:=CenterRadiusDelaunayPolytopeGeneral(GramMat, EXT);
  ListSolutionsSameRadius:=[];
  ListSolutionsSameEXT:=[];
  for eVect in BuildSet(n, [0..TheMod-1])
  do
    if eVect*eVect>0 then
      NewBasis:=SubspaceCompletion([eVect], Length(eVect));
      Add(NewBasis, eVect/TheMod);
      NewGramMat:=NewBasis*GramMat*TransposedMat(NewBasis);
      eBigBasis:=FuncCreateBigMatrix(ListWithIdenticalEntries(n,0),NewBasis);
      eInvBasis:=Inverse(eBigBasis);
      EXTbig:=EXT*eInvBasis;
      eCenterBig:=CP.Center*eInvBasis;
      eCenterBigRed:=eCenterBig{[2..n+1]};
      CVP:=CVPVallentinProgram(NewGramMat, eCenterBigRed);
      if CVP.TheNorm=CP.SquareRadius and Length(CVP.ListVect)<>Length(EXT) then
        Add(ListSolutionsSameRadius, NewGramMat);
      fi;
      if CVP.TheNorm=CP.SquareRadius and Length(CVP.ListVect)=Length(EXT) then
        Add(ListSolutionsSameEXT, NewGramMat);
      fi;
    fi;
  od;
  return rec(ListSolutionsSameRadius:=ListSolutionsSameRadius, ListSolutionsSameEXT:=ListSolutionsSameEXT);
end;


GetExtensionOfPerfectDelaunay:=function(EXTinp, TheMod)
  local EXT, n, GramMat, DistMat, GRP, ListGen, eGen, eBigMat, eMat, ListOrbitSuperspaces, ListSolutionsSameRadius, ListSolutionsSameEXT, eOrbit, eInvMat, EXTbig, eCenterBig, CVP, CP, NewGramMat, eCenterBigRed;
  EXT:=GetPresentationGeneratingDelaunay(EXTinp);
  n:=Length(EXT[1])-1;
  GramMat:=FuncExtreme(EXT).GramMatrix;
  DistMat:=DistanceMatrixDelaunay(GramMat, EXT);
  GRP:=AutomorphismGroupEdgeColoredGraph(DistMat);
  CP:=CenterRadiusDelaunayPolytopeGeneral(GramMat, EXT);
  ListGen:=[];
  for eGen in GeneratorsOfGroup(GRP)
  do
    eBigMat:=FindTransformation(EXT, EXT, eGen);
    eMat:=FuncExplodeBigMatrix(eBigMat).MatrixTransformation;
    Add(ListGen, eMat);
  od;
  GRP:=Group(ListGen);
  ListOrbitSuperspaces:=GetSuperlattices(GramMat, GRP, TheMod);
  ListSolutionsSameRadius:=[];
  ListSolutionsSameEXT:=[];
  for eOrbit in ListOrbitSuperspaces
  do
    eMat:=eOrbit.Basis;
    eBigMat:=FuncCreateBigMatrix(ListWithIdenticalEntries(n,0),eMat);
    eInvMat:=Inverse(eBigMat);
    NewGramMat:=eMat*GramMat*TransposedMat(eMat);
    EXTbig:=EXT*eInvMat;
    eCenterBig:=CP.Center*eInvMat;
    eCenterBigRed:=eCenterBig{[2..n+1]};
    CVP:=CVPVallentinProgram(NewGramMat, eCenterBigRed);
    if CVP.TheNorm=CP.SquareRadius and Length(CVP.ListVect)<>Length(EXT) then
      Add(ListSolutionsSameRadius, NewGramMat);
    fi;
    if CVP.TheNorm=CP.SquareRadius and Length(CVP.ListVect)=Length(EXT) then
      Add(ListSolutionsSameEXT, NewGramMat);
    fi;
  od;
  return rec(ListSolutionsSameRadius:=ListSolutionsSameRadius, ListSolutionsSameEXT:=ListSolutionsSameEXT);
end;


WriteFaceInequalities:=function(ListOrbitDelaunay, eCase)
  local n, ListInequalities, iOrb, ExtractedBasis, EXT, ListInformations, iExt, TheInfo, RedIneq, pos, eAdj, AdjacentEXT, eVect, TheVert, FindPositionVector;
  n:=Length(eCase.Basis[1]);
  ListInequalities:=[];
  FindPositionVector:=function(eVect)
    local i;
    for i in [1..Length(ListInequalities)]
    do
      if IsProportionalVector(ListInequalities[i], eVect)=true then
        return i;
      fi;
    od;
    return fail;
  end;
  ListInformations:=[];
  for iOrb in [1..Length(ListOrbitDelaunay)]
  do
    EXT:=ListOrbitDelaunay[iOrb].EXT;
    ExtractedBasis:=RowReduction(EXT, n+1).EXT;
    for eAdj in ListOrbitDelaunay[iOrb].Adjacencies
    do
      AdjacentEXT:=ListOrbitDelaunay[eAdj.iDelaunay].EXT*eAdj.eBigMat;
      TheVert:=Difference(Set(AdjacentEXT), Set(EXT))[1];
      RedIneq:=VoronoiLinearInequality(ExtractedBasis, TheVert, eCase.Basis);
      TheInfo:=eAdj;
      TheInfo.Input:=iOrb;
      pos:=FindPositionVector(RedIneq);
      if pos=fail then
        Add(ListInequalities, RedIneq);
        Add(ListInformations, [TheInfo]);
      else
        Add(ListInformations[pos], TheInfo);
      fi;
    od;
  od;
  return rec(ListInequalities:=ListInequalities, 
             ListInformations:=ListInformations);
end;




AntisymmetryConstruction:=function(EXT, GramMat)
  local deltaI, RefSqrRadius, CurrentDelta, j, CurrentSquareRad, ListRelevantEXT, n, CP, Vcent, H, TheDen, ListSqrRadius, i, NewCent, TheCVP, EXTnew, TheSpann, NSP, MinDelta, NewGramMat, eProd, NewEXT, eCenter, EXT2, EXT1, NewCenter, LowerEst, CPtest, EXTret;
  if Set(List(EXT, x->x[1]))<>[1] then 
    Error("First coordinate should be 1!");
  fi;
  n:=Length(GramMat);
  CP:=CenterRadiusDelaunayPolytopeGeneral(GramMat, EXT);
  Vcent:=CP.Center{[2..n+1]};
  RefSqrRadius:=CP.SquareRadius;
  H:=RemoveFractionPlusCoef(Vcent);
  TheDen:=NumeratorRat(H.TheMult);
  ListSqrRadius:=[];
  CurrentDelta:=0;
  CurrentSquareRad:=RefSqrRadius;
  ListRelevantEXT:=[];
  NewCenter:=Concatenation([1], ListWithIdenticalEntries(n,0),[1/2]);
  i:=2;
  while(true)
  do
    i:=i+1;
    if i > TheDen then
      break;
    fi;
    NewCent:=-Vcent+2*(i-1)*Vcent;
    LowerEst:=CurrentDelta*(i-1-1/2)^2;
    if LowerEst > CurrentSquareRad then
      break;
    fi;
    Print("LowerEst insufficient\n");
    TheCVP:=CVPVallentinProgram(GramMat, NewCent);
    EXT1:=List(TheCVP.ListVect, x->Concatenation([1], x, [i-1]));
    EXT2:=List(EXT1, x->2*NewCenter-x);
    EXTnew:=Concatenation(EXT1, EXT2);
    if TheCVP.TheNorm < RefSqrRadius then
      deltaI:=(TheCVP.TheNorm-RefSqrRadius)/(1/4- (i-1-1/2)^2);
      Print("deltaI=", deltaI, "\n");
      if deltaI > CurrentDelta then
        Print("Now CurrentDelta=", CurrentDelta, "\n");
        CurrentDelta:=deltaI;
        CurrentSquareRad:=TheCVP.TheNorm+deltaI*(i-1-1/2)^2;
        ListRelevantEXT:=ShallowCopy(EXTnew);
      elif deltaI=CurrentDelta then
        Append(ListRelevantEXT, EXTnew);
        Print("Now |ListRelevantEXT|=", Length(ListRelevantEXT), "\n");
      fi;
    fi;
  od;
  Print("|ListRelevantEXT|=", Length(ListRelevantEXT), "\n");
  EXT1:=List(EXT, x->Concatenation(x, [1]));
  EXT2:=List(EXT1, x->2*NewCenter-x);
  Print("|EXT1|=", Length(EXT1), "  |EXT2|=", Length(EXT2), "\n");
  EXTnew:=Concatenation(EXT1, EXT2);
  EXTret:=Concatenation(ListRelevantEXT, EXTnew);
  Print("Now |EXTret|=", Length(EXTret), "\n");
  if CurrentDelta=0 then
    TheSpann:=Concatenation(IdentityMat(n), [2*Vcent]);
    NSP:=Rational_BaseIntMat(TheSpann);
    eCenter:=SolutionMat(NSP, -Vcent);
    NewGramMat:=NSP*GramMat*TransposedMat(NSP);
    TheCVP:=CVPVallentinProgram(NewGramMat, eCenter);
    NewEXT:=List(TheCVP.ListVect, x->Concatenation([1],x));
    return rec(GramMat:=NewGramMat, EXT:=NewEXT, eCase:=1);
  else
    NewGramMat:=NullMat(n+1,n+1);
    for i in [1..n]
    do
      for j in [1..n]
      do
        NewGramMat[i][j]:=GramMat[i][j];
      od;
    od;
    eProd:=-2*Vcent*GramMat;
    for i in [1..n]
    do
      NewGramMat[i][n+1]:=eProd[i];
      NewGramMat[n+1][i]:=eProd[i];
    od;
    NewGramMat[n+1][n+1]:=CurrentDelta+(2*Vcent)*GramMat*(2*Vcent);
    #
    CPtest:=CenterRadiusDelaunayPolytopeGeneral(NewGramMat, EXTret);
    #
    return rec(GramMat:=NewGramMat, EXT:=EXTret, eCase:=2);
  fi;
end;



