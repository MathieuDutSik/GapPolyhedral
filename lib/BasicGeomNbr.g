FileVectorSplit_V1:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"VectorSplitting.prog");
FileVectorSplit_V2:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"GRP_VectorSplitting");
FileSeparation:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"Separation");






ComputeOrbitsVectors_General:=function(TheGRP, TheDim, TheModulo, opt_version)
  local FileInput, FileOutput, output, nbGen, eGen, TheRead;
  FileInput:=Filename(POLYHEDRAL_tmpdir,"VectSplit.input");
  FileOutput:=Filename(POLYHEDRAL_tmpdir,"VectSplit.output");
  RemoveFileIfExist(FileInput);
  RemoveFileIfExist(FileOutput);
  output:=OutputTextFile(FileInput, true);
  AppendTo(output, TheDim, "\n");
  AppendTo(output, TheModulo, "\n");
  nbGen:=Length(GeneratorsOfGroup(TheGRP));
  AppendTo(output, nbGen, "\n");
  for eGen in GeneratorsOfGroup(TheGRP)
  do
    WriteMatrix(output, eGen);
  od;
  CloseStream(output);
  #
  if opt_version=1 then
    Exec(FileVectorSplit_V1, " ", FileInput, " ", FileOutput);
  fi;
  if opt_version=2 then
    Exec(FileVectorSplit_V2, " ", FileInput, " ", FileOutput);
  fi;
  TheRead:=ReadAsFunction(FileOutput)();
  RemoveFile(FileInput);
  RemoveFile(FileOutput);
  return TheRead;
end;


ComputeOrbitsVectors:=function(TheGRP, TheDim, TheModulo)
  local opt_version;
  opt_version:=2;
  return ComputeOrbitsVectors_General(TheGRP, TheDim, TheModulo, opt_version);
end;


#
#
# Get orbits of super lattices L2 such that L2/L1 is isomorphic
# to Z/TheMod Z
GetSuperlattices:=function(GramMat, GRP, TheMod)
  local TheDim, ListOrb, ListSuperspaces, eOrb, eVect, NewBasis, NewGramMat;
  TheDim:=Length(GramMat);
  ListOrb:=ComputeOrbitsVectors(GRP, TheDim, TheMod);
  ListSuperspaces:=[];
  for eOrb in ListOrb
  do
    eVect:=eOrb.eVect;
    if eVect*eVect>0 then
      NewBasis:=SubspaceCompletion([eVect], Length(eVect));
      Add(NewBasis, eVect/TheMod);
      NewGramMat:=NewBasis*GramMat*TransposedMat(NewBasis);
      Add(ListSuperspaces, rec(GramMat:=NewGramMat, OrbitSize:=eOrb.OrbitSize, Basis:=NewBasis, eVect:=eVect));
    fi;
  od;
  return ListSuperspaces;
end;




GetBasisSpaceSpecMod:=function(eVect, TheMod)
  local TheBasis, LS, TheMult, TheVectCoef, TotBasis;
  TheBasis:=NullspaceIntMat(TransposedMat([eVect]));
  LS:=GcdVector(eVect);
  TheMult:=TheMod/LS.TheGcd;
  TheVectCoef:=TheMult*LS.ListCoef;
  TotBasis:=[TheVectCoef];
  Append(TotBasis, ShallowCopy(TheBasis));
  return TotBasis;
end;



#
#
# Get orbits of sub lattices L2 such that L1/L2 is isomorphic
# to Z/TheMod Z
#
# The technique is to work in the dual.

GetSublattices:=function(GramMat, GRP, TheMod)
  local TheDim, ListOrb, eOrb, eVect, NewGramMat, NewListGens, CongruentGRP, ListSubspaces, TheBasis, eGen;
  TheDim:=Length(GramMat);
  for eGen in GeneratorsOfGroup(GRP)
  do
    if GramMat<>eGen*GramMat*TransposedMat(eGen) then
      Error("GramMat is not preserved");
    fi;
  od;
  NewListGens:=List(GeneratorsOfGroup(GRP), TransposedMat);
  CongruentGRP:=Group(NewListGens);
  ListOrb:=ComputeOrbitsVectors(CongruentGRP, TheDim, TheMod);
  ListSubspaces:=[];
  for eOrb in ListOrb
  do
    eVect:=eOrb.eVect;
    if eVect*eVect>0 then
      TheBasis:=GetBasisSpaceSpecMod(eVect, TheMod);
      NewGramMat:=TheBasis*GramMat*TransposedMat(TheBasis);
      Add(ListSubspaces, rec(GramMat:=NewGramMat, OrbitSize:=eOrb.OrbSize, Basis:=TheBasis, eVect:=eVect));
    fi;
  od;
  return ListSubspaces;
end;










#
#
# this function takes as argument a distance vector d in HYPnand return
# true if the corresponding Delaunay polytope has full dimension
DistanceMatrixToGramMatrix:=function(DistMat)
  local iCol, iLin, n, GramMatrix, HypDim;
  HypDim:=Length(DistMat);
  n:=HypDim-1;
  GramMatrix:=NullMat(n,n);
  for iCol in [1..n]
  do
    for iLin in [1..n]
    do
      GramMatrix[iCol][iLin]:=-(DistMat[iCol+1][iLin+1]-DistMat[iCol+1][1]-DistMat[iLin+1][1])/2;
    od;
  od;
  return GramMatrix;
end;

NorderApproximationSqrt2:=function(N)
  local eApprox, i;
  eApprox:=1;
  for i in [1..N]
  do
    eApprox:=2+1/eApprox;
  od;
  return 1+1/eApprox;
end;




#
#
# We search for a matrix M such that
# M P1(i)  =P2(i) M
# i.e. one that realize the equivalence between representations
# defined by ListMat1 and ListMat2
ShurEquivalence:=function(ListMat1, ListMat2)
  local n, ListCoeff, iLin, iCol, FuncPos, ListEquations, iMat, eMat1, eMat2, i, j, TheEquation, k, pos1, pos2, ListEquivalence, eSol, VR, U, LineForm;
  n:=Length(ListMat1[1]);
  ListCoeff:=[];
  for iLin in [1..n]
  do
    for iCol in [1..n]
    do
      Add(ListCoeff, [iLin, iCol]);
    od;
  od;
  FuncPos:=function(i,j)
    return Position(ListCoeff, [i,j]);
  end;
  ListEquations:=[];
  for iMat in [1..Length(ListMat1)]
  do
    eMat1:=ListMat1[i];
    eMat2:=ListMat2[i];
    for i in [1..n]
    do
      for j in [1..i]
      do
        TheEquation:=ListWithIdenticalEntries(Length(ListCoeff), 0);
        for k in [1..n]
        do
          pos1:=FuncPos(i,k);
          TheEquation[pos1]:=TheEquation[pos1]+eMat1[k][j];
          pos2:=FuncPos(k,j);
          TheEquation[pos2]:=TheEquation[pos2]-eMat2[i][k];
        od;
        AddSet(ListEquations, TheEquation);
      od;
    od;
  od;
  ListEquivalence:=[];
  for eSol in NullspaceMat(TransposedMat(ListEquations))
  do
    VR:=RemoveFraction(eSol);
    U:=[];
    for i in [1..n]
    do
      LineForm:=[];
      for j in [1..n]
      do
        Add(LineForm, VR[FuncPos(i,j)]);
      od;
      Add(U, LineForm);
    od;
    Add(ListEquivalence, U);
  od;
  return ListEquivalence;
end;











GramMatrixToDistanceMatrix:=function(GramMat)
  local DistMat, n, iCol, iLin;
  n:=Length(GramMat);
  DistMat:=NullMat(n+1,n+1);
  for iCol in [2..n+1]
  do
    DistMat[iCol][1]:=GramMat[iCol-1][iCol-1];
    DistMat[1][iCol]:=GramMat[iCol-1][iCol-1];
  od;
  for iCol in [2..n+1]
  do
    for iLin in [2..n+1]
    do
      DistMat[iCol][iLin]:=GramMat[iCol-1][iCol-1]+GramMat[iLin-1][iLin-1]-2*GramMat[iCol-1][iLin-1];
    od;
  od;
  return DistMat;
end;


InvariantSpace:=function(TheBasis, MatrixGRP)
  local ListEqua, eGen, eMat;
  ListEqua:=[];
  for eGen in GeneratorsOfGroup(MatrixGRP)
  do
    eMat:=List(TheBasis, x->SolutionMat(TheBasis, x*eGen));
    Append(ListEqua, eMat-IdentityMat(Length(TheBasis)));
  od;
  return List(NullspaceMat(TransposedMat(ListEqua)), x->x*TheBasis);
end;

IntersectionSubspace:=function(eSubspace1, eSubspace2)
  local NSP;
  NSP:=[];
  if Length(eSubspace1.ListVect)=0 then
    Append(NSP, IdentityMat(eSubspace1.n));
  else
    Append(NSP, NullspaceMat(TransposedMat(eSubspace1.ListVect)));
  fi;
  if Length(eSubspace2.ListVect)=0 then
    Append(NSP, IdentityMat(eSubspace1.n));
  else
    Append(NSP, NullspaceMat(TransposedMat(eSubspace2.ListVect)));
  fi;
  if Length(NSP)=0 then
    return rec(n:=eSubspace1.n, ListVect:=IdentityMat(eSubspace1.n));
  fi;
  return rec(n:=eSubspace1.n, ListVect:=NullspaceMat(TransposedMat(NSP)));
end;

IsEqualVectorSpace:=function(eSubspace1, eSubspace2)
  local eVect;
  if eSubspace1.n<>eSubspace2.n then
    Error("The subspaces are not part of the same space");
  fi;
  if Length(eSubspace1.ListVect)<>Length(eSubspace2.ListVect) then
    return false;
  fi;
  for eVect in eSubspace1.ListVect
  do
    if SolutionMat(eSubspace2.ListVect, eVect)=fail then
      return false;
    fi;
  od;
  return true;
end;

IntersectionOrbitSubspace:=function(eSubspace, MatrixGRP)
  local eSubspaceRet, NewSubspace, eGen, FuncImage;
  eSubspaceRet:=ShallowCopy(eSubspace);
  FuncImage:=function(eSubspace, eGen)
    return rec(n:=eSubspace.n, ListVect:=List(eSubspace.ListVect, x->x*eGen));
  end;
  while(true)
  do
    NewSubspace:=ShallowCopy(eSubspaceRet);
    for eGen in GeneratorsOfGroup(MatrixGRP)
    do
      NewSubspace:=IntersectionSubspace(NewSubspace, FuncImage(eSubspaceRet, eGen));
    od;
    if Length(NewSubspace.ListVect)=Length(eSubspaceRet.ListVect) then
      return eSubspaceRet;
    fi;
    eSubspaceRet:=ShallowCopy(NewSubspace);
  od;
end;



VectorSpaceSpannedUnionOrbit:=function(eSubspace, MatrixGRP)
  local GetOrthogonal, CongrGRP, fSubspace;
  GetOrthogonal:=function(eSubspace)
    local NSP;
    if Length(eSubspace.ListVect) > 0 then
      NSP:=NullspaceMat(TransposedMat(eSubspace.ListVect));
      return rec(n:=eSubspace.n, ListVect:=NSP);
    else
      return rec(n:=eSubspace.n, ListVect:=IdentityMat(eSubspace.n));
    fi;
  end;
  CongrGRP:=Group(List(GeneratorsOfGroup(MatrixGRP), x->TransposedMat(x)));
  fSubspace:=IntersectionOrbitSubspace(GetOrthogonal(eSubspace), CongrGRP);
  return GetOrthogonal(fSubspace);
end;



CanonicalSymmetricBasis:=function(n)
  local MatDim, TheBasisMatrix, ListVect, TheVectorSpace, i, eVect;
  MatDim:=n*(n+1)/2;
  TheBasisMatrix:=[];
  ListVect:=[];
  for i in [1..MatDim]
  do
    eVect:=ListWithIdenticalEntries(MatDim,0);
    eVect[i]:=1;
    Add(TheBasisMatrix, VectorToSymmetricMatrix(eVect, n));
    Add(ListVect, eVect);
  od;
  TheVectorSpace:=rec(n:=MatDim, ListVect:=ListVect);
  return rec(TheBasisMatrix:=TheBasisMatrix, MatDim:=MatDim, TheVectorSpace:=TheVectorSpace);
end;

BasesCommutingMatrices:=function(ListMat)
  local n, ListLine, eMat, i, j, eLine, k, idx1, idx2, NSP, TheBasis, eNSP, eBasisMat, idx;
  n:=Length(ListMat[1]);
  ListLine:=[];
  for eMat in ListMat
  do
    for i in [1..n]
    do
      for j in [1..n]
      do
        eLine:=ListWithIdenticalEntries(n*n,0);
        for k in [1..n]
        do
          idx1:=k+(j-1)*n;
          idx2:=i+(k-1)*n;
          eLine[idx1]:=eLine[idx1] + eMat[i][k];
          eLine[idx2]:=eLine[idx2] - eMat[k][j];
        od;
        Add(ListLine, eLine);
      od;
    od;
  od;
  NSP:=NullspaceMat(TransposedMat(ListLine));
  TheBasis:=[];
  for eNSP in NSP
  do
    eBasisMat:=NullMat(n,n);
    for i in [1..n]
    do
      for j in [1..n]
      do
        idx:=i+(j-1)*n;
        eBasisMat[i][j]:=eNSP[idx];
      od;
    od;
    if First(ListMat, x->x*eBasisMat<>eBasisMat*x)<>fail then
      Error("Error in commuting function");
    fi;
    Add(TheBasis, eBasisMat);
  od;
  return TheBasis;
end;



#
#
# return a basis of matrices satisfying to
# U*M*TransposedMat(U)=M for every U in the
# provided MatrixGenerators
InvariantFormDutourVersion:=function(MatrixGenerators)
  local ListCoeff, iLin, iCol, FuncPos, ListEquations, eGen, i, j, k, l, TheEquation, pos, ListInvariantForm, eMat, U, LineForm, VR, n;
  n:=Length(MatrixGenerators[1]);
  if Length(MatrixGenerators)=0 then
    return IdentityMat(n*(n+1)/2);
  fi;
  ListCoeff:=[];
  for iLin in [1..n]
  do
    for iCol in [1..iLin]
    do
      Add(ListCoeff, [iLin, iCol]);
    od;
  od;
  FuncPos:=function(i,j)
    if i<j then
      return Position(ListCoeff, [j,i]);
    else
      return Position(ListCoeff, [i,j]);
    fi;
  end;
  ListEquations:=[];
  for eGen in MatrixGenerators
  do
    U:=eGen;
    for i in [1..n]
    do
      for j in [1..i]
      do
        TheEquation:=ListWithIdenticalEntries(Length(ListCoeff), 0);
        TheEquation[FuncPos(i,j)]:=1;
        for k in [1..n]
        do
          for l in [1..n]
          do
            pos:=FuncPos(k,l);
            TheEquation[pos]:=TheEquation[pos]-U[i][k]*U[j][l];
          od;
        od;
        AddSet(ListEquations, TheEquation);
      od;
    od;
  od;
  ListInvariantForm:=[];
  for eMat in NullspaceMat(TransposedMat(ListEquations))
  do
    VR:=RemoveFraction(eMat);
    U:=[];
    for i in [1..n]
    do
      LineForm:=[];
      for j in [1..n]
      do
        Add(LineForm, VR[FuncPos(i,j)]);
      od;
      Add(U, LineForm);
    od;
    Add(ListInvariantForm, U);
  od;
  return ListInvariantForm;
end;


InvariantAntisymmetricForm:=function(MatrixGenerators)
  local ListCoeff, iLin, iCol, FuncPos, ListEquations, eGen, i, j, k, l, TheEquation, pos, ListInvariantForm, eVect, LineForm, n, nbCoeff, eRec, eForm;
  n:=Length(MatrixGenerators[1]);
  if Length(MatrixGenerators)=0 then
    return IdentityMat(n*(n+1)/2);
  fi;
  ListCoeff:=[];
  for iLin in [2..n]
  do
    for iCol in [1..iLin-1]
    do
      Add(ListCoeff, [iLin, iCol]);
    od;
  od;
  nbCoeff:=Length(ListCoeff);
  FuncPos:=function(iLin,iCol)
    if iCol<iLin then
      return rec(pos:=Position(ListCoeff, [iLin, iCol]), sign:=1);
    else
      return rec(pos:=Position(ListCoeff, [iCol, iLin]), sign:=-1);
    fi;
  end;
  ListEquations:=[];
  for eGen in MatrixGenerators
  do
    for i in [2..n]
    do
      for j in [1..i-1]
      do
        TheEquation:=ListWithIdenticalEntries(nbCoeff, 0);
        TheEquation[FuncPos(i,j).pos]:=1;
        for k in [1..n]
        do
          for l in [1..n]
          do
            if k<>l then
              eRec:=FuncPos(k,l);
              TheEquation[eRec.pos]:=TheEquation[eRec.pos] - eRec.sign*eGen[i][k]*eGen[j][l];
            fi;
          od;
        od;
        AddSet(ListEquations, TheEquation);
      od;
    od;
  od;
  ListInvariantForm:=[];
  for eVect in NullspaceIntMat(TransposedMat(ListEquations))
  do
    eForm:=[];
    for i in [1..n]
    do
      LineForm:=[];
      for j in [1..n]
      do
        if i=j then
          Add(LineForm, 0);
        else
          eRec:=FuncPos(i,j);
          Add(LineForm, eVect[eRec.pos]*eRec.sign);
        fi;
      od;
      Add(eForm, LineForm);
    od;
    for eGen in MatrixGenerators
    do
      if eGen*eForm*TransposedMat(eGen)<>eForm then
        Error("The form is not invariant, please panic");
      fi;
    od;
    Add(ListInvariantForm, eForm);
  od;
  return ListInvariantForm;
end;





FuncCreateBigMatrix:=function(eTrans, eMat)
  local NewMat, eV;
  NewMat:=[];
  Add(NewMat, Concatenation([1], eTrans));
  for eV in eMat
  do
    Add(NewMat, Concatenation([0], eV));
  od;
  return NewMat;
end;

FuncExplodeBigMatrix:=function(BigMat)
  local n, eTrans, eMatrix, iLine;
  n:=Length(BigMat)-1;
  eTrans:=BigMat[1]{[2..n+1]};
  eMatrix:=List([2..n+1], x->BigMat[x]{[2..n+1]});
  return rec(eTrans:=eTrans, MatrixTransformation:=eMatrix);
end;








ShortVectorDutourVersion:=function(GramMat, eNorm)
  local H, eNormRed, GramMatRed, SHV, ListVector, iV, eV;
  H:=RemoveFractionMatrixPlusCoef(GramMat);
  eNormRed:=LowerInteger(eNorm*H.TheMult);
  GramMatRed:=H.TheMat;
  if IsPositiveDefiniteSymmetricMatrix(GramMatRed)=false then
    Error("Matrix should be positive definite");
  fi;
  SHV:=ShortestVectors(GramMatRed, eNormRed);
  ListVector:=[];
  for iV in [1..Length(SHV.vectors)]
  do
    if SHV.norms[iV] <= eNormRed then
      eV:=SHV.vectors[iV];
      Add(ListVector, eV);
      Add(ListVector, -eV);
    fi;
  od;
  return ListVector;
end;

ShortestVectorDutourVersion:=function(GramMat)
  local n, MiniN, MiniN2, ListVector, iV, SHV, eV, GramMatRed, MiniN3, MiniWork, TheRemainder;
  GramMatRed:=RemoveFractionMatrix(GramMat);
  n:=Length(GramMatRed);
  if IsPositiveDefiniteSymmetricMatrix(GramMatRed)=false then
    Error("Matrix should be positive definite");
  fi;
  TheRemainder:=LLLReducedGramMat(GramMatRed).remainder;
  MiniN:=Minimum(List([1..n], x->GramMatRed[x][x]));
  MiniN2:=Minimum(List([1..n], x->TheRemainder[x][x]));
  MiniWork:=Minimum(MiniN, MiniN2);
  SHV:=ShortestVectors(GramMatRed, MiniWork);
  MiniN3:=Minimum(SHV.norms);
  ListVector:=[];
  for iV in [1..Length(SHV.vectors)]
  do
    if SHV.norms[iV]=MiniN3 then
      eV:=SHV.vectors[iV];
      Add(ListVector, eV);
      Add(ListVector, -eV);
    fi;
  od;
  return ListVector;
end;


IsLatticeWellRounded:=function(GramMat)
  local n, SHV;
  n:=Length(GramMat);
  SHV:=ShortestVectorDutourVersion(GramMat);
  if RankMat(SHV)=n then
    return true;
  fi;
  return false;
end;


WellRoundedInformation:=function(GramMat)
  local n, SHV, IsWellRounded, TheIndex;
  n:=Length(GramMat);
  SHV:=ShortestVectorDutourVersion(GramMat);
  if RankMat(SHV)=n then
    IsWellRounded:=true;
    TheIndex:=DeterminantMat(BaseIntMat(SHV));
  else
    IsWellRounded:=false;
    TheIndex:="undef";
  fi;
  return rec(IsWellRounded:=IsWellRounded, TheIndex:=TheIndex);
end;










GroupFacToGroupEXT:=function(EXT, FAC, GroupFac)
  local ListTotal, iExt, ListInc, ExtMov, u, NewGens, IsLegalMove, pos, eMov;
  ListTotal:=[];
  for iExt in [1..Length(EXT)]
  do
    ListInc:=Filtered([1..Length(FAC)], x->FAC[x]*EXT[iExt]=0);
    Add(ListTotal, ListInc);
  od;
  IsLegalMove:=function(eMov)
    ExtMov:=[];
    for iExt in [1..Length(EXT)]
    do
      pos:=Position(ListTotal, OnSets(ListTotal[iExt], eMov));
      if pos=fail then
        return false;
      fi;
      ExtMov[iExt]:=pos;
    od;
    return ExtMov;
  end;
  NewGens:=[];
  for u in GeneratorsOfGroup(GroupFac)
  do
    eMov:=IsLegalMove(u);
    if eMov<>false then
      Add(NewGens, PermList(eMov));
    fi;
  od;
  if Length(NewGens)>0 then
    return Group(NewGens);
  else
    return Group(());
  fi;
end;



FindingTranslateImage:=function(EXTbig, EXTsmall)
  local ListRepresentation, u, Vtrans, LER, eV;
  ListRepresentation:=[];
  for u in EXTbig
  do
    Vtrans:=u-EXTsmall[1];
    LER:=[];
    for eV in EXTsmall
    do
      Add(LER, eV+Vtrans);
    od;
    if IsSubset(Set(EXTbig), Set(LER))=true then
      Add(ListRepresentation, LER);
    fi;
  od;
  return ListRepresentation;
end;



BuildDistanceVector:=function(Polytope, SubGraph)
  local n, VCT, i, j, S, iCol, l;
  n:=Length(SubGraph);
  VCT:=[0];
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      S:=0;
      for iCol in [1..Length(Polytope[1])]
      do
        l:=Polytope[SubGraph[i]][iCol]-Polytope[SubGraph[j]][iCol];
        S:=S+l*l;
      od;
      Add(VCT, S);
    od;
  od;
  return RemoveFraction(VCT);
end;


BuildDistanceVectorList:=function(Polytope, ListOfSubGraph)
  local List, i;
  List:=[];
  for i in [1..Length(ListOfSubGraph)]
  do
    List[i]:=BuildDistanceVector(Polytope, ListOfSubGraph[i]);
  od;
  return List;
end;




# Computes the largest t so that the list X is a spherical-t-design
# in the Euclidean space defined by Q
# 
# t: positive integer
# X: list of d-dimensional vectors
# Q: positive definite matrix with d rows and d columns
# 
# assumption: xQx is constant for all x in X
# 
# for mathematics: see e.g. Goethals, Seidel
__GetExponent:=function(n, k)
  local s, i;
  if k mod 2 = 0 then
    s:=1;
    for i in [1..k-1]
    do
      if i mod 2 = 1 then
        s:=s*i/(n+(i-1));
      fi;
    od;
    return s;
  else
    return 0;
  fi;
end;



SphericalDesignLevel:=function(EXT, GramMat)
  local k, sk, skxi, n, Rsqr, eEXT, fEXT, scal;
  n:=Length(GramMat);
  Rsqr:=EXT[1]*GramMat*EXT[1];
  k:=0;
  repeat
    k:=k+1;
    Print("Checking for spherical-", k, "-design\n");
    sk:=0;
    for eEXT in EXT
    do
      skxi:=0;
      for fEXT in EXT
      do
        scal:=eEXT*GramMat*fEXT/Rsqr;
        skxi:=skxi+scal^k;
      od;
      skxi:=skxi/Length(EXT);
      sk:=sk+skxi-__GetExponent(n, k);
    od;
  until sk <> 0;
  return k-1;
end;




SphericalDesignLevelGroup:=function(EXT, GroupEXT, GramMat)
  local k, sk, skxi, n, Rsqr, eEXT, fEXT, scal, OrbSize, O, iOrb, ListLenOrb, rnk;
  n:=Length(GramMat);
  Rsqr:=EXT[1]*GramMat*EXT[1];
  O:=Orbits(GroupEXT, [1..Length(EXT)], OnPoints);
  ListLenOrb:=List(O, Length);
  rnk:=RankMat(EXT);
  k:=0;
  repeat
    k:=k+1;
    Print("Checking for spherical-", k, "-design\n");
    if k>2 and rnk=1 then
      return 1;
    fi;
    sk:=0;
    for iOrb in [1..Length(O)]
    do
      OrbSize:=Length(O[iOrb]);
      eEXT:=EXT[O[iOrb][1]];
      skxi:=0;
      for fEXT in EXT
      do
        scal:=eEXT*GramMat*fEXT/Rsqr;
        skxi:=skxi+scal^k;
      od;
      skxi:=skxi/Length(EXT);
      sk:=sk+OrbSize*(skxi-__GetExponent(n, k));
    od;
  until sk <> 0;
  return k-1;
end;


Enumerate2laminationsOrbitwise:=function(EXT, PermGRP)
  local AffBasis, ListCoord, EXTnew, n, FileIn, FileOutput, FileOutputMeta, FileGroup, FileSupport, FileScratch, FileOutput2, FileError1, FileError2, output, nbVertM, ListRes, ListSolutions, eSet, V, eSol;
  AffBasis:=CreateAffineBasis(EXT);
  ListCoord:=List(Difference(Set(EXT), Set(AffBasis)), x->SolutionMat(AffBasis, x));
  EXTnew:=List(EXT, x->SolutionMat(AffBasis, x));
  #
  n:=Length(EXT[1])-1;
  FileIn:=Filename(POLYHEDRAL_tmpdir, "2lam_INPUT");
  FileOutput:=Filename(POLYHEDRAL_tmpdir, "2lam_Data");
  FileOutputMeta:=Filename(POLYHEDRAL_tmpdir, "2lam_MetaData");
  FileGroup:=Filename(POLYHEDRAL_tmpdir, "2lam_Group");
  FileSupport:=Filename(POLYHEDRAL_tmpdir, "2lam_Support");
  FileScratch:=Filename(POLYHEDRAL_tmpdir, "2lam_Scratch");
  FileOutput2:=Filename(POLYHEDRAL_tmpdir, "2lam_Output");
  FileError1:=Filename(POLYHEDRAL_tmpdir, "2lam_Error1");
  FileError2:=Filename(POLYHEDRAL_tmpdir, "2lam_Error2");
  #
  RemoveFileIfExist(FileIn);
  RemoveFileIfExist(FileOutput);
  RemoveFileIfExist(FileOutputMeta);
  RemoveFileIfExist(FileGroup);
  RemoveFileIfExist(FileSupport);
  RemoveFileIfExist(FileScratch);
  RemoveFileIfExist(FileOutput2);
  RemoveFileIfExist(FileError1);
  RemoveFileIfExist(FileError2);
  #
  output:=OutputTextFile(FileIn, true);
  AppendTo(output, n+1, "\n");
  nbVertM:=Length(ListCoord);
  AppendTo(output, nbVertM, "\n");
  WriteMatrix(output, ListCoord);
  CloseStream(output);
  #
  OutputGroup(PermGRP, Length(EXTnew), FileGroup);
  #
  output:=OutputTextFile(FileSupport, true);
  WriteMatrix(output, EXTnew);
  CloseStream(output);
  #
  Exec(FileSeparation, " ", FileIn, " ", FileOutput, " ", FileOutputMeta, " 2> ", FileError1);
  #
  Exec(FileIsoReduction, " ", FileOutput, " ", FileOutputMeta, " ", FileGroup, " ", FileSupport, " ", FileScratch, " ", FileOutput2, " 2> ", FileError2);
  ListRes:=ReadAsFunction(FileOutput2)();
  #
  ListSolutions:=[];
  for eSet in ListRes
  do
    if Length(eSet)<>0 and Length(eSet)<>Length(EXTnew) then
      V:=ListWithIdenticalEntries(Length(EXTnew), 0);
      V{eSet}:=ListWithIdenticalEntries(Length(eSet), 1);
      eSol:=SolutionMat(TransposedMat(EXT), V);
      Add(ListSolutions, eSol);
    fi;
  od;
  #
  RemoveFile(FileIn);
  RemoveFile(FileOutput);
  RemoveFile(FileOutputMeta);
  RemoveFile(FileGroup);
  RemoveFile(FileSupport);
  RemoveFile(FileScratch);
  RemoveFile(FileOutput2);
  RemoveFile(FileError1);
  RemoveFile(FileError2);
  return ListSolutions;
end;




Enumerate2laminations:=function(EXT)
  local AffBasis, ListCoord, EXTnew, n, FileIn, FileOutput, FileOutputMeta, FileError1, output, nbVertM, ListRes, ListSolutions, eSet, V, eSol, eVect;
  AffBasis:=CreateAffineBasis(EXT);
  ListCoord:=List(Difference(Set(EXT), Set(AffBasis)), x->SolutionMat(AffBasis, x));
  EXTnew:=List(EXT, x->SolutionMat(AffBasis, x));
  #
  n:=Length(EXT[1])-1;
  FileIn:=Filename(POLYHEDRAL_tmpdir, "2lam_INPUT");
  FileOutput:=Filename(POLYHEDRAL_tmpdir, "2lam_Data");
  FileOutputMeta:=Filename(POLYHEDRAL_tmpdir, "2lam_MetaData");
  FileError1:=Filename(POLYHEDRAL_tmpdir, "2lam_Error1");
  #
  RemoveFileIfExist(FileIn);
  RemoveFileIfExist(FileOutput);
  RemoveFileIfExist(FileOutputMeta);
  RemoveFileIfExist(FileError1);
  #
  output:=OutputTextFile(FileIn, true);
  AppendTo(output, n+1, "\n");
  nbVertM:=Length(ListCoord);
  AppendTo(output, nbVertM, "\n");
  WriteMatrix(output, ListCoord);
  CloseStream(output);
  #
  Exec(FileSeparation, " ", FileIn, " ", FileOutput, " ", FileOutputMeta, " 2> ", FileError1);
  #
  ListRes:=ReadVectorFile(FileOutput);
  #
  ListSolutions:=[];
  for eVect in ListRes
  do
    eSet:=Filtered([1..Length(EXTnew)], x->EXTnew[x]*eVect=0);
    if Length(eSet)<>0 and Length(eSet)<>Length(EXTnew) then
      V:=ListWithIdenticalEntries(Length(EXTnew), 0);
      V{eSet}:=ListWithIdenticalEntries(Length(eSet), 1);
      eSol:=SolutionMat(TransposedMat(EXT), V);
      Add(ListSolutions, eSol);
    fi;
  od;
  #
  RemoveFile(FileIn);
  RemoveFile(FileOutput);
  RemoveFile(FileOutputMeta);
  RemoveFile(FileError1);
  return ListSolutions;
end;


GetListPermGensFromListPermMatr:=function(EXT, ListPermMatr)
  local ePermSort, ListPermGens, eMatrGen, ePermGen;
  ePermSort:=Inverse(SortingPerm(EXT));
  ListPermGens:=[];
  for eMatrGen in ListPermMatr
  do
    ePermGen:=SortingPerm(EXT*eMatrGen)*ePermSort;
    Add(ListPermGens, ePermGen);
  od;  
  return ListPermGens;
end;


#
#
TestForPolytopeLaminationDelaunay:=function(EXTinp, StabEXT)
  local NewListGens, TheDim, CongruentGRP, ListOrb, rnk, EXTred, eOrb, eVect, EXTred1, EXTred2, EXT1, EXT2, FuncEnumerate4lamination, nbVert, StabPermGens, GroupEXT, ListPermGens, IsRankAtLeast4, FuncEnumerateLaminationOrbitwise, FuncEnumerateLamination, IsRankAtLeast3, LaminationNumberDetermination, ListDiff, TheMatr, EXT, ePermGen, eMatrGen, ePermSort;
  TheDim:=Length(EXTinp[1])-1;
  StabPermGens:=GeneratorsOfGroup(StabEXT);
  NewListGens:=List(StabPermGens, x->TransposedMat(FuncExplodeBigMatrix(x).MatrixTransformation));
  ePermSort:=Inverse(SortingPerm(EXTinp));
  ListPermGens:=[];
  for eMatrGen in StabPermGens
  do
    ePermGen:=SortingPerm(EXTinp*eMatrGen)*ePermSort;
    Add(ListPermGens, ePermGen);
  od;  
  #
  ListDiff:=List(EXTinp, x->x{[2..TheDim+1]}-EXTinp[1]{[2..TheDim+1]});
  TheMatr:=Concatenation([EXTinp[1]], List(GetZbasis(ListDiff), x->Concatenation([0], x)));
  EXT:=EXTinp*Inverse(TheMatr);
  rnk:=RankMat(EXT);
  if rnk<>Length(EXT[1]) then
    Error("The polytope should be full dimensional");
  fi;
  GroupEXT:=Group(ListPermGens);
  nbVert:=Length(EXT);
  CongruentGRP:=Group(NewListGens);
  ListOrb:=ComputeOrbitsVectors(CongruentGRP, TheDim, 2);
  IsRankAtLeast3:=function()
    local List2lam;
    List2lam:=Enumerate2laminationsOrbitwise(EXT, GroupEXT);
    if Length(List2lam)=0 then
      return true;
    fi;
    return false;
  end;
  IsRankAtLeast4:=function()
    local test, EXTred, eOrb, eVect, EXTred1, EXTred2, EXT1, EXT2;
    test:=true;
    EXTred:=List(EXT, x->x{[2..TheDim+1]});
    for eOrb in ListOrb
    do
      eVect:=eOrb.eVect;
      if eVect*eVect>0 then
        EXTred1:=Filtered(EXTred, x->x*eVect mod 2=0);
        EXTred2:=Filtered(EXTred, x->x*eVect mod 2=1);
        EXT1:=List(EXTred1, x->Concatenation([1], x));
        EXT2:=List(EXTred2, x->Concatenation([1], x));
        if RankMat(EXT1)< rnk or RankMat(EXT2) < rnk then
          test:=false;
        fi;
      fi;
    od;
    return test;
  end;
  FuncEnumerateLaminationOrbitwise:=function()
    local ListOrbitSolutions4, ListOrbitSolutions5, eOrb, eVect, ListIdx1, EXTred1, ListIdx2, EXTred2, ListSiz, MinSiz, PermStab, EXT1, EXT2, List2lam1, List2lam2, fVect, ListVal1, ListVal2, PermStab1, PermStab2;
    ListOrbitSolutions4:=[];
    ListOrbitSolutions5:=[];
    EXTred:=List(EXT, x->x{[2..TheDim+1]});
    for eOrb in ListOrb
    do
      eVect:=eOrb.eVect;
      if eVect*eVect>0 then
        ListIdx1:=Filtered([1..nbVert], x->EXTred[x]*eVect mod 2=0);
        EXTred1:=EXTred{ListIdx1};
        ListIdx2:=Filtered([1..nbVert], x->EXTred[x]*eVect mod 2=1);
        EXTred2:=EXTred{ListIdx2};
        ListSiz:=[Length(ListIdx1), Length(ListIdx2)];
        MinSiz:=Minimum(ListSiz);
        if Position(ListSiz, MinSiz)=1 then
          PermStab:=Stabilizer(GroupEXT, ListIdx1, OnSets);
        else
          PermStab:=Stabilizer(GroupEXT, ListIdx2, OnSets);
        fi;
        PermStab1:=SecondReduceGroupAction(PermStab, ListIdx1);
        PermStab2:=SecondReduceGroupAction(PermStab, ListIdx2);
        EXT1:=List(EXTred1, x->Concatenation([1], x));
        EXT2:=List(EXTred2, x->Concatenation([1], x));
        List2lam1:=Enumerate2laminationsOrbitwise(EXT1, PermStab1);
        List2lam2:=Enumerate2laminationsOrbitwise(EXT2, PermStab2);
        for fVect in List2lam1
        do
          ListVal1:=Collected(List(EXT1, x->x*fVect));
          if Length(ListVal1)<>2 then
            Error("We have inconsistency in the lamination computation 1");
          fi;
          ListVal2:=Collected(List(EXT2, x->x*fVect));
          if Length(ListVal2)=2 then
            Add(ListOrbitSolutions4, fVect);
          fi;
          if Length(ListVal2)=3 then
            Add(ListOrbitSolutions5, fVect);
          fi;
        od;
        for fVect in List2lam2
        do
          ListVal2:=Collected(List(EXT2, x->x*fVect));
          if Length(ListVal2)<>2 then
            Error("We have inconsistency in the lamination computation 2");
          fi;
          ListVal1:=Collected(List(EXT1, x->x*fVect));
          if Length(ListVal1)=3 then
            Add(ListOrbitSolutions5, fVect);
          fi;
        od;
      fi;
    od;  
    return rec(ListOrbitSolutions4:=ListOrbitSolutions4, ListOrbitSolutions5:=ListOrbitSolutions5);
  end;
  FuncEnumerateLamination:=function()
    local ListSolutions4, ListSolutions5, eOrb, eVect, ListIdx1, EXTred1, ListIdx2, EXTred2, PermStab, EXT1, EXT2, List2lam1, List2lam2, fVect, ListVal1, ListVal2, ListSolutions6;
    ListSolutions4:=[];
    ListSolutions5:=[];
    ListSolutions6:=[];
    EXTred:=List(EXT, x->x{[2..TheDim+1]});
    for eOrb in ListOrb
    do
      eVect:=eOrb.eVect;
      if eVect*eVect>0 then
        ListIdx1:=Filtered([1..nbVert], x->EXTred[x]*eVect mod 2=0);
        EXTred1:=EXTred{ListIdx1};
        ListIdx2:=Filtered([1..nbVert], x->EXTred[x]*eVect mod 2=1);
        EXTred2:=EXTred{ListIdx2};
        EXT1:=List(EXTred1, x->Concatenation([1], x));
        EXT2:=List(EXTred2, x->Concatenation([1], x));
        List2lam1:=Enumerate2laminations(EXT1);
        List2lam2:=Enumerate2laminations(EXT2);
        for fVect in List2lam1
        do
          ListVal1:=Collected(List(EXT1, x->x*fVect));
          if Length(ListVal1)<>2 then
            Error("We have inconsistency in the lamination computation 3");
          fi;
          ListVal2:=Collected(List(EXT2, x->x*fVect));
          if Length(ListVal2)=2 then
            Add(ListSolutions4, fVect);
          fi;
          if Length(ListVal2)=3 then
            Add(ListSolutions5, fVect);
          fi;
          if Length(ListVal2)=4 then
            Add(ListSolutions6, fVect);
          fi;
        od;
        for fVect in List2lam2
        do
          ListVal2:=Collected(List(EXT2, x->x*fVect));
          if Length(ListVal2)<>2 then
            Error("We have inconsistency in the lamination computation 4");
          fi;
          ListVal1:=Collected(List(EXT1, x->x*fVect));
          if Length(ListVal1)=3 then
            Add(ListSolutions5, fVect);
          fi;
          if Length(ListVal1)=4 then
            Add(ListSolutions6, fVect);
          fi;
        od;
      fi;
    od;
    return rec(ListSolutions4:=ListSolutions4, ListSolutions5:=ListSolutions5, ListSolution6:=ListSolutions6);
  end;
  LaminationNumberDetermination:=function()
    local TheEnum;
    if IsRankAtLeast3()=false then
      return "2";
    fi;
    if IsRankAtLeast4()=false then
      return "3";
    fi;
    TheEnum:=FuncEnumerateLamination();
    if Length(TheEnum.ListSolutions4)>0 then
      return "4";
    fi;
    if Length(TheEnum.ListSolutions5)>0 then
      return "5";
    fi;
    if Length(TheEnum.ListSolutions6)>0 then
      return "6";
    fi;
    return "6 or more";
  end;
  return rec(IsRankAtLeast4:=IsRankAtLeast4,
             LaminationNumberDetermination:=LaminationNumberDetermination, 
             FuncEnumerateLaminationOrbitwise:=FuncEnumerateLaminationOrbitwise, 
             FuncEnumerateLamination:=FuncEnumerateLamination);
end;
