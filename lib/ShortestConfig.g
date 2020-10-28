FilePrimeRefinement:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"SHORT_CheckPrimeRealizability");
FileShortReduceIsomorphyGAP:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"SHORT_ReduceVectorFamilyGAP");
FileConvertPariMollienOutput:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"ConvertPariMollien");
FileReadFrinakFiles:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"ReadFrinakFiles");
FileReadFrinakFiles2:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"ReadFrinakFiles2");

SHORT_GetScalMatGeneral:=function(eMat)
  local eMatExt, p, n, ScalMat_NT, i, iR, j, jR, eDiff, eMatRes, NSP, TotalBasis, ListSol, eDet, ScalMat_Lin, eLine, ListDiag, ListOffDiag, eInv, ScalMat, rnk;
  eMatExt:=Concatenation(eMat, -eMat);
  p:=Length(eMat[1]);
  n:=Length(eMat);
  ScalMat_NT:=NullMat(2*n,2*n);
  for i in [1..2*n]
  do
    if i>n then
      iR:=i-n;
    else
      iR:=i;
    fi;
    for j in [1..2*n]
    do
      if j>n then
        jR:=j-n;
      else
        jR:=j;
      fi;
      eDiff:=Difference([1..n], Set([iR, jR]));
      eMatRes:=eMat{eDiff};
      rnk:=RankMat(eMatRes);
      if rnk<p then
        NSP:=NullspaceIntMat(TransposedMat(eMatRes));
        TotalBasis:=NullspaceIntMat(TransposedMat(NSP));
      else
        TotalBasis:=IdentityMat(p);
      fi;
      ListSol:=List(eMatRes, x->SolutionMat(TotalBasis,x));
      eDet:=AbsInt(DeterminantMat(BaseIntMat(ListSol)));
      ScalMat_NT[i][j]:=[eDet, rnk];
    od;
  od;
  ScalMat_Lin:=VectorConfigurationFullDim_ScalarMat(eMatExt);
  ScalMat:=[];
  ListOffDiag:=[];
  for i in [1..2*n]
  do
    eLine:=[];
    for j in [1..2*n]
    do
      eInv:=[ScalMat_Lin[i][j], ScalMat_NT[i][j]];
      Add(eLine, eInv);
      if i<>j then
        Add(ListOffDiag, eInv);
      fi;
    od;
    Add(ScalMat, eLine);
  od;
  ListDiag:=List([1..2*n], x->ScalMat[x][x]);
  return rec(ScalMatrix:=ScalMat, eInv:=rec(CollDiag:=Collected(ListDiag), CollOffDiag:=Collected(ListOffDiag)));
end;

SHORT_GetAntipodals:=function(eMat)
  return Concatenation(eMat, -eMat);
end;

SHORT_GetHyperoctahedralLikeSuperGroup:=function(eMatExt)
  local n, eMat, TheInv;
  n:=Length(eMatExt)/2;
  eMat:=eMatExt{[1..n]};
  TheInv:=SHORT_GetScalMatGeneral(eMat);
  return AutomorphismGroupColoredGraph(TheInv.ScalMatrix);
end;

SHORT_Rank:=function(SHV)
  local TheMat, eLine, eProj, eProjVect;
  TheMat:=[];
  for eLine in SHV
  do
    eProj:=TransposedMat([eLine]) * [eLine];
    eProjVect:=SymmetricMatrixToVector(eProj);
    Add(TheMat, eProjVect);
  od;
  return RankMat(TheMat);
end;



SHORT_GetTransposition:=function(eMatExt)
  local n, ListPerm, ePair, i, j, iP, jP, ePerm, RetMat;
  n:=Length(eMatExt)/2;
  ListPerm:=[];
  for ePair in Combinations([1..n],2)
  do
    i:=ePair[1];
    j:=ePair[2];
    iP:=i+n;
    jP:=j+n;
    ePerm:=(i,j)(iP,jP);
    RetMat:=FindTransformation(eMatExt, eMatExt, ePerm);
    if RetMat<>fail then
      if IsIntegralMat(RetMat)=true then
        Add(ListPerm, ePerm);
      fi;
    fi;
  od;
  return ListPerm;
end;

SHORT_GetSignOper:=function(eMatExt)
  local n, ListPerm, eVect, eList, ePerm, i, RetMat;
  n:=Length(eMatExt)/2;
  ListPerm:=[];
  for eVect in BuildSet(n, [0,1])
  do
    eList:=ListWithIdenticalEntries(2*n,0);
    for i in [1..n]
    do
      if eVect[i]=0 then
        eList[i]:=i;
        eList[i+n]:=i+n;
      else
        eList[i]:=i+n;
        eList[i+n]:=i;
      fi;
    od;
    ePerm:=PermList(eList);
    RetMat:=FindTransformation(eMatExt, eMatExt, ePerm);
    if RetMat<>fail then
      if IsIntegralMat(RetMat)=true then
        Add(ListPerm, ePerm);
      fi;
    fi;
  od;
  return ListPerm;
end;

SHORT_GetEasyPartStabilizer:=function(eMatExt)
  local ListPerm;
  ListPerm:=[];
  Append(ListPerm, SHORT_GetTransposition(eMatExt));
  Append(ListPerm, SHORT_GetSignOper(eMatExt));
  return Group(ListPerm);
end;

SHORT_GetCandidateCyclic_Kernel:=function(n, d)
  local MaxVal, ListCand, i, iDim, NewListCand, eCand, LastVal, NewCand;
  MaxVal:=LowerInteger(d/2);
  ListCand:=[];
  for i in [1..MaxVal]
  do
    Add(ListCand, [i]);
  od;
  for iDim in [2..n]
  do
    NewListCand:=[];
    for eCand in ListCand
    do
      LastVal:=eCand[iDim-1];
      for i in [LastVal..MaxVal]
      do
        NewCand:=Concatenation(eCand, [i]);
	Add(NewListCand, NewCand);
      od;
    od;
    ListCand:=Set(NewListCand);
  od;
  return ListCand;
end;


SHORT_GetLLLreduction_Kernel:=function(eSHV)
  local TheGram, GetGram, res, TheRemainder, TheTrans, InvTrans, Pmat, eSHVred;
  GetGram:=function(uSHV)
    local n, TheGram, eVect, eRankOne;
    n:=Length(uSHV[1]);
    TheGram:=NullMat(n,n);
    for eVect in uSHV
    do
      eRankOne:=TransposedMat([eVect]) * [eVect];
      TheGram:=TheGram + eRankOne;
    od;
    return TheGram;
  end;
  TheGram:=GetGram(eSHV);
  res:=LLLReducedGramMat(TheGram);
  TheRemainder:=res.remainder;
  TheTrans:=res.transformation;
  InvTrans:=Inverse(TheTrans);
  if InvTrans*TheRemainder*TransposedMat(InvTrans)<>TheGram then
    Error("Error in LLL computation");
  fi;
  Pmat:=TransposedMat(TheTrans);
  eSHVred:=eSHV*Pmat;
  if GetGram(eSHVred)<>TheRemainder then
    Error("Matrix error somewhere");
  fi;
  return rec(SHVred:=eSHVred, ReductionMatrix:=Pmat);
end;

SHORT_GetLLLreduction:=function(eSHV)
  return SHORT_GetLLLreduction_Kernel(eSHV).SHVred;
end;




SHORT_GetCandidateCyclic:=function(n, d)
  local ListCand, nbCand, iCand, eCand, mult, ListStatus, Canonicalization, pos, eSet, eProd, NewCand;
  if IsPrime(d)=false then
    Print("d=", d, "\n");
    Error("The number d should be prime");
  fi;
  ListCand:=Set(SHORT_GetCandidateCyclic_Kernel(n, d));
  nbCand:=Length(ListCand);
  Print("nbCand=", nbCand, "\n");
  ListStatus:=ListWithIdenticalEntries(nbCand, 1);
  Canonicalization:=function(fCand)
    local RetCand, i, eVal, nVal, ePerm;
    RetCand:=[];
    for i in [1..n]
    do
      eVal:=fCand[i];
      if eVal > d/2 then
        nVal:=d-eVal;
      else
        nVal:=eVal;
      fi;
      Add(RetCand, nVal);
    od;
    ePerm:=SortingPerm(RetCand);
    return Permuted(RetCand, ePerm);
  end;
  for iCand in [1..nbCand]
  do
    if ListStatus[iCand]=1 then
      eCand:=ListCand[iCand];
      for mult in [2..d-1]
      do
        eProd:=List(eCand, x->x*mult mod d);
        NewCand:=Canonicalization(eProd);
	pos:=Position(ListCand, NewCand);
	if pos=fail then
	  Error("Inconsistency in the computation");
	fi;
	if pos<>iCand then
          ListStatus[pos]:=0;
	fi;
      od;
    fi;
  od;
  eSet:=Filtered([1..nbCand], x->ListStatus[x]=1);
  Print("|eSet|=", Length(eSet), "\n");
  return ListCand{eSet};
end;



SHORT_GetCandidateCyclic_Optimized:=function(n, d)
  local MaxVal, ListCand, i, iDim, Canonicalization, IsMinimal, NewListCand, eCand, LastVal, NewCand;
  MaxVal:=LowerInteger(d/2);
  ListCand:=[ [1] ];
  if IsPrime(d)=false then
    Print("d=", d, "\n");
    Error("The number d should be prime");
  fi;
  Canonicalization:=function(fCand)
    local RetCand, i, eVal, nVal, ePerm;
    RetCand:=[];
    for eVal in fCand
    do
      if eVal > d/2 then
        nVal:=d-eVal;
      else
        nVal:=eVal;
      fi;
      Add(RetCand, nVal);
    od;
    ePerm:=SortingPerm(RetCand);
    return Permuted(RetCand, ePerm);
  end;
  IsMinimal:=function(eCand)
    local mult, eProd;    
    for mult in [2..d-1]
    do
      eProd:=List(eCand, x->x*mult mod d);
      NewCand:=Canonicalization(eProd);
      if NewCand < eCand then
        return false;
      fi;
    od;
    return true;
  end;
  for iDim in [2..n]
  do
    NewListCand:=[];
    for eCand in ListCand
    do
      LastVal:=eCand[iDim-1];
      for i in [LastVal..MaxVal]
      do
        NewCand:=Concatenation(eCand, [i]);
        if IsMinimal(NewCand) then
          Add(NewListCand, NewCand);
	fi;
      od;
    od;
    ListCand:=Set(NewListCand);
  od;
  return ListCand;
end;











SHORT_GetStabilizer_V1:=function(eMat)
  local eMatExt, TheSuperGroup, TheSubGroup, FuncMembership, PermGrp, ListGenRed, PermGrpRed, ListMatrGens, MatrGrpRed;
  eMatExt:=SHORT_GetAntipodals(eMat);
  TheSuperGroup:=SHORT_GetHyperoctahedralLikeSuperGroup(eMatExt);
#  Print("|TheSuperGroup|=", Order(TheSuperGroup), "\n");
  TheSubGroup:=SHORT_GetEasyPartStabilizer(eMatExt);
#  Print("|TheSubGroup|=", Order(TheSubGroup), "\n");
  FuncMembership:=function(ePerm)
    local RetMat;
    RetMat:=FindTransformation(eMatExt, eMatExt, ePerm);
    if IsIntegralMat(RetMat)=true then
      return true;
    fi;
    return false;
  end;
  PermGrp:=GetIntermediateGroup(TheSubGroup, TheSuperGroup, FuncMembership);
  ListGenRed:=SmallGeneratingSet(PermGrp);
  PermGrpRed:=Group(ListGenRed);
  ListMatrGens:=List(ListGenRed, x->FindTransformation(eMatExt, eMatExt, x));
  MatrGrpRed:=Group(ListMatrGens);
  return rec(MatrGrp:=MatrGrpRed, PermGrp:=PermGrpRed);
end;

SHORT_IsEquivalence:=function(eMat1, eMat2, eEquivMat)
  local HMat1, HMat2;
  HMat1:=Concatenation(eMat1, -eMat1);
  HMat2:=Concatenation(eMat2, -eMat2);
  if Set(HMat1*eEquivMat)<>Set(HMat2) then
    return false;
  fi;
  return true;
end;

SHORT_GetInformation:=function(Vmat)
  local n, Amat, eV, TheGramMat, InvariantBasis, SHVdisc;
  n:=Length(Vmat[1]);
  Amat:=NullMat(n,n);
  for eV in Vmat
  do
    Amat:=Amat + TransposedMat([eV])*[eV];
  od;
  TheGramMat:=Inverse(Amat);
  InvariantBasis:=__ExtractInvariantZBasisShortVectorNoGroup(TheGramMat);
  for eV in Vmat
  do
    if Position(InvariantBasis, 2*eV)<>fail then
      Error("Vectors in the invariant basis should be irreducibles");
    fi;
  od;
  if First(InvariantBasis, x->IsVectorIrreducible(x)=false)<>fail then
    Error("The vectors of the invariant basis should be irreducible");
  fi;
  SHVdisc:=Concatenation(InvariantBasis, 2*Vmat, -2*Vmat);
  return rec(GramMat:=TheGramMat, SHVdisc:=SHVdisc);
end;


SHORT_GetStabilizer:=function(Vmat)
  local eRec, GRPmat, VmatExt, ListMatrGens, ListPermGens, GRPperm, GRPpermRed, ListPermGensRed, PositionRed, phi, phiRed;
  if Length(Intersection(Set(Vmat), Set(-Vmat))) > 0 then
    Error("Vmat contains some vector and its opposite");
  fi;
  eRec:=SHORT_GetInformation(Vmat);
  GRPmat:=ArithmeticAutomorphismMatrixFamily_Nauty([eRec.GramMat], eRec.SHVdisc);
  VmatExt:=SHORT_GetAntipodals(Vmat);
  ListMatrGens:=GeneratorsOfGroup(GRPmat);
  ListPermGens:=List(ListMatrGens, x->PermList(List(VmatExt, y->Position(VmatExt, y*x))));
  GRPperm:=Group(ListPermGens);
  phi:=GroupHomomorphismByImagesNC(GRPperm, GRPmat, ListPermGens, ListMatrGens);
  PositionRed:=function(eVect)
    local pos;
    pos:=Position(Vmat, eVect);
    if pos<>fail then
      return pos;
    fi;
    return Position(Vmat, -eVect);
  end;
  ListPermGensRed:=List(ListMatrGens, x->PermList(List(Vmat, y->PositionRed(y*x))));
  GRPpermRed:=Group(ListPermGensRed);
  phiRed:=GroupHomomorphismByImagesNC(GRPperm, GRPpermRed, ListPermGens, ListPermGensRed);
  return rec(VmatExt:=VmatExt, MatrGrp:=GRPmat, PermGrp:=GRPperm, phi:=phi, phiRed:=phiRed, PermGrpRed:=GRPpermRed);
end;


SHORT_GetStabilizerCone:=function(eSHV)
  local RecGRP, ListRankOneMatExt, nbVext, ListRankOne, ListRankOneProj, nbV, ListSubset, ListOrigin, iV, eSet, GRP, ListPermGens, ListMatrGens, eGen, eList, fSet, pos, ePerm, eMatr, PermGRPcone, MatrGRPcone, phi, eRank;
  RecGRP:=SHORT_GetStabilizer(eSHV);
  ListRankOneMatExt:=List(RecGRP.VmatExt, x->SymmetricMatrixToVector(TransposedMat([x]) * [x]));
  nbVext:=Length(RecGRP.VmatExt);
  ListRankOne:=Set(ListRankOneMatExt);
  ListRankOneProj:=ColumnReduction(ListRankOne).EXT;
  eRank:=Length(ListRankOneProj[1]);
  nbV:=Length(ListRankOne);
  ListSubset:=List(ListRankOne, x->Filtered([1..nbVext], y->ListRankOneMatExt[y]=x));
  ListOrigin:=ListWithIdenticalEntries(nbVext, 0);
  for iV in [1..nbV]
  do
    eSet:=ListSubset[iV];
    ListOrigin{eSet}:=ListWithIdenticalEntries(Length(eSet), iV);
  od;
  GRP:=RecGRP.PermGrp;
  ListPermGens:=[];
  ListMatrGens:=[];
  for eGen in GeneratorsOfGroup(GRP)
  do
    eList:=[];
    for eSet in ListSubset
    do
      fSet:=OnSets(eSet, eGen);
      pos:=Position(ListSubset, fSet);
      Add(eList, pos);
    od;
    ePerm:=PermList(eList);
    eMatr:=FindTransformation(ListRankOneProj, ListRankOneProj, ePerm);
    Add(ListPermGens, ePerm);
    Add(ListMatrGens, eMatr);
  od;
  PermGRPcone:=Group(ListPermGens);
  MatrGRPcone:=Group(ListMatrGens);
  phi:=GroupHomomorphismByImagesNC(PermGRPcone, MatrGRPcone, ListPermGens, ListMatrGens);
  return rec(RecGRP:=RecGRP,
             ListSubset:=ListSubset,
             ListOrigin:=ListOrigin,
             eRank:=eRank, 
             PermGRPcone:=PermGRPcone,
             MatrGRPcone:=MatrGRPcone,
             phi:=phi);
end;

GetCyclicComplex:=function(n)
  return Concatenation(IdentityMat(n), [ListWithIdenticalEntries(n,1)]);
end;




SHORT_SAGE_PrintPsigmaSum:=function(output, eSHV, RecGRPcone)
  local CJ, eCJ, eSize, eG, eMat, TheOrd;
#  RecGRPcone:=SHORT_GetStabilizerCone(eSHV);
#  Print("|RecGRPcone.RecGRP.PermGrp|=", Order(RecGRPcone.RecGRP.PermGrp), "\n");
  AppendTo(output, "poly=0\n");
  AppendTo(output, "IdMat = identity_matrix(", RecGRPcone.eRank, ")\n");
  CJ:=ConjugacyClasses(RecGRPcone.PermGRPcone);
  for eCJ in CJ
  do
    eSize:=Size(eCJ);
    eG:=Representative(eCJ);
    eMat:=Image(RecGRPcone.phi, eG);
    AppendTo(output, "a=");
    SAGE_PrintMatrix(output, eMat);
    AppendTo(output, "\n");
    AppendTo(output, "b = IdMat - t*a\n");
    AppendTo(output, "TheDet = b.determinant()\n");
    AppendTo(output, "poly = poly + ", eSize, "/TheDet\n");
    AppendTo(output, "\n");
  od;
  TheOrd:=Order(RecGRPcone.PermGRPcone);
#  Print("TheOrd=", TheOrd, "\n");
  AppendTo(output, "PsigmaSum = poly / ", TheOrd, "\n");
end;



SHORT_PARI_PrintPsigmaSum:=function(output, eSHV, RecGRPcone)
  local CJ, eCJ, eSize, eG, eMat, TheOrd;
#  RecGRPcone:=SHORT_GetStabilizerCone(eSHV);
#  Print("|RecGRPcone.RecGRP.PermGrp|=", Order(RecGRPcone.RecGRP.PermGrp), "\n");
  AppendTo(output, "poly=0\n");
  AppendTo(output, "IdMat = matid(", RecGRPcone.eRank, ")\n");
  CJ:=ConjugacyClasses(RecGRPcone.PermGRPcone);
  for eCJ in CJ
  do
    eSize:=Size(eCJ);
    eG:=Representative(eCJ);
    eMat:=Image(RecGRPcone.phi, eG);
    AppendTo(output, "a=");
    PARI_PrintMatrix(output, eMat);
    AppendTo(output, "\n");
    AppendTo(output, "b = IdMat - t*a\n");
    AppendTo(output, "TheDet = matdet(b)\n");
    AppendTo(output, "poly = poly + ", eSize, " / TheDet\n");
    AppendTo(output, "\n");
  od;
  TheOrd:=Order(RecGRPcone.PermGRPcone);
#  Print("TheOrd=", TheOrd, "\n");
  AppendTo(output, "PsigmaSum = poly / ", TheOrd, "\n");
end;


SHORT_GetIndividualMollienSeries:=function(eSHV)
  local FileInput, FileOutput, FileRead, FileErr, RecGRPcone, output, TheCommand1, TheCommand2, eRes;
  FileInput :=Filename(POLYHEDRAL_tmpdir,"Mollien.pari");
  FileOutput:=Filename(POLYHEDRAL_tmpdir,"Mollien.out");
  FileRead:=Filename(POLYHEDRAL_tmpdir,"Mollien.read");
  FileErr:=Filename(POLYHEDRAL_tmpdir,"Mollien.err");
  RemoveFileIfExist(FileInput);
  RecGRPcone:=SHORT_GetStabilizerCone(eSHV);
  output:=OutputTextFile(FileInput, true);
  SHORT_PARI_PrintPsigmaSum(output, eSHV, RecGRPcone);
  AppendTo(output, "print(numerator(PsigmaSum))\n");
  AppendTo(output, "eR =factor(denominator(PsigmaSum))\n");
  AppendTo(output, "print(eR)\n");
  AppendTo(output, "print(taylor(PsigmaSum,t,10))\n");
  AppendTo(output, "quit\n");
  CloseStream(output);
  #
  TheCommand1:=Concatenation("gp ", FileInput, " > ", FileOutput, " 2> ", FileErr);
#  Print("TheCommand1=", TheCommand1, "\n");
  Exec(TheCommand1);
  #
  TheCommand2:=Concatenation(FileConvertPariMollienOutput, " ", FileOutput, " ", FileRead);
#  Print("TheCommand2=", TheCommand2, "\n");
  Exec(TheCommand2);
  #
  eRes:=ReadAsFunction(FileRead)();
  RemoveFileIfExist(FileInput);
  RemoveFileIfExist(FileOutput);
  RemoveFileIfExist(FileRead);
  RemoveFileIfExist(FileErr);
  return eRes;
end;





SHORT_GetInformationPair:=function(Vmat1, Vmat2)
  local n, Amat, eV, TheGramMat, InvariantBasis, SHVdisc;
  n:=Length(Vmat1[1]);
  Amat:=NullMat(n,n);
  for eV in Vmat1
  do
    Amat:=Amat + TransposedMat([eV])*[eV];
  od;
  TheGramMat:=Inverse(Amat);
  InvariantBasis:=__ExtractInvariantZBasisShortVectorNoGroup(TheGramMat);
  if First(InvariantBasis, x->IsVectorIrreducible(x)=false)<>fail then
    Error("The vectors of the invariant basis should be irreducible");
  fi;
  SHVdisc:=Concatenation(InvariantBasis, 2*Vmat1, -2*Vmat1, 3*Vmat2, -3*Vmat2);
  return rec(GramMat:=TheGramMat, SHVdisc:=SHVdisc);
end;


SHORT_GetStabilizerPair:=function(Vmat1, Vmat2)
  local eRec, GRPmat, VmatExt, ListMatrGens, ListPermGens, GRPperm;
  eRec:=SHORT_GetInformationPair(Vmat1, Vmat2);
  GRPmat:=ArithmeticAutomorphismMatrixFamily_Nauty([eRec.GramMat], eRec.SHVdisc);
  VmatExt:=SHORT_GetAntipodals(Vmat1);
  ListMatrGens:=GeneratorsOfGroup(GRPmat);
  ListPermGens:=List(ListMatrGens, x->PermList(List(VmatExt, y->Position(VmatExt, y*x))));
  GRPperm:=Group(ListPermGens);
  return rec(VmatExt:=VmatExt, MatrGrp:=GRPmat, PermGrp:=GRPperm);
end;



SHORT_TestEquivalence_V1:=function(eMat1, eMat2)
  local n, RecGrp1, RecGrp2, eMatExt1, eMatExt2, TheSuperGroup2, TheInv1, TheInv2, eEquiv, i, gPerm, GRPintTrans1, LDCS, eDCS, eRepr, ePerm, RetMat, eDet1, eDet2;
  n:=Length(eMat1);
  eDet1:=AbsInt(DeterminantMat(BaseIntMat(eMat1)));
  eDet2:=AbsInt(DeterminantMat(BaseIntMat(eMat2)));
  if eDet1<>eDet2 then
    return false;
  fi;
  RecGrp1:=SHORT_GetStabilizer(eMat1);
  RecGrp2:=SHORT_GetStabilizer(eMat2);
  eMatExt1:=SHORT_GetAntipodals(eMat1);
  eMatExt2:=SHORT_GetAntipodals(eMat2);
  TheSuperGroup2:=SHORT_GetHyperoctahedralLikeSuperGroup(eMatExt2);
  TheInv1:=SHORT_GetScalMatGeneral(eMat1);
  TheInv2:=SHORT_GetScalMatGeneral(eMat2);
  eEquiv:=IsIsomorphicColoredGraph(TheInv1.ScalMatrix, TheInv2.ScalMatrix);
  if eEquiv=false then
    return false;
  fi;
  gPerm:=PermList(eEquiv);
  GRPintTrans1:=Group(List(GeneratorsOfGroup(RecGrp1.PermGrp), x->Inverse(gPerm)*x*gPerm));
  LDCS:=DoubleCosets(TheSuperGroup2, GRPintTrans1, RecGrp2.PermGrp);
  for eDCS in LDCS
  do
    eRepr:=Representative(eDCS);
    ePerm:=gPerm*eRepr;
    RetMat:=FindTransformation(eMatExt1, eMatExt2, ePerm);
    if IsIntegralMat(RetMat)=true and AbsInt(DeterminantMat(RetMat))=1 then
      if SHORT_IsEquivalence(eMat1, eMat2, RetMat)=false then
        Error("Dramatic error");
      fi;
      return rec(RetMat:=RetMat, ePerm:=ePerm);
    fi;
  od;
  return false;
end;





SHORT_TestEquivalence:=function(eMat1, eMat2)
  local eRec1, eRec2, eMatExt1, eMatExt2, eEquiv, eList, ePerm, eEquivInv;
  eRec1:=SHORT_GetInformation(eMat1);
  eRec2:=SHORT_GetInformation(eMat2);
  eMatExt1:=SHORT_GetAntipodals(eMat1);
  eMatExt2:=SHORT_GetAntipodals(eMat2);
  eEquiv:=ArithmeticEquivalenceMatrixFamily_Nauty([eRec1.GramMat], eRec1.SHVdisc, [eRec2.GramMat], eRec2.SHVdisc);
  if eEquiv=false then
    return false;
  fi;
  eEquivInv:=Inverse(eEquiv);
  eList:=List(eMatExt1, x->Position(eMatExt2, x*eEquivInv));
  ePerm:=PermList(eList);
  if ePerm=fail then
    Error("Bug to be solved in SHORT_TestEquivalence");
  fi;
  return rec(RetMat:=eEquivInv, ePerm:=ePerm);
end;

SHORT_Invariant:=function(eMat)
  local eRec;
  eRec:=SHORT_GetInformation(eMat);
  return KernelGetInvariantGram(eRec.GramMat, eRec.SHVdisc);
end;



SHORT_CleanAntipodality:=function(ListVect)
  local ListVectRet, eVect;
  ListVectRet:=[];
  for eVect in ListVect
  do
    if Position(ListVectRet, eVect)=fail and Position(ListVectRet, -eVect)=fail then
      Add(ListVectRet, eVect);
    fi;
  od;
  return ListVectRet;
end;

SHORT_GetIneq_Tspace:=function(eVect, TheBasis)
  local eIneq, eVectBas;
  eIneq:=[-1];
  for eVectBas in TheBasis
  do
    Add(eIneq, eVect*eVectBas*eVect);
  od;
  return eIneq;
end;


SHORT_GetIneq_Tspace_centralcone:=function(eVect, TheBasis)
  local eIneq, eVectBas;
  eIneq:=[-2];
  for eVectBas in TheBasis
  do
    Add(eIneq, eVect*eVectBas*eVect);
  od;
  return eIneq;
end;


SHORT_GetShortZeroOrNegativeVector_General:=function(eMatSec, CritNorm)
  local NSP, NewVect, List_NewVectCand, NewVect_short, NewVect_float, NewVect_infinite, List_NormL1, TheMin, pos, StrictIneq, NeedNonZero;
  if RankMat(eMatSec)<Length(eMatSec) then
    NSP:=NullspaceMat(eMatSec);
    NewVect:=RemoveFraction(NSP[1]);
    Print("NSP : NewVect=", NewVect, "\n");
    return NewVect;
  else
    Print("CritNorm=", CritNorm, "\n");
    # There are a number of issues in choosing the right vector
    # eigenvalue based seem to work the best but are exposed to
    # floating point error allowing bad vectors to be built.
    # 
    # The solution seems to be a combination of all. L1 norm seems
    # as good as any other for quality evaluation since anyway the 
    # best NewVect is very obvious
    List_NewVectCand:=[];
    #
    NewVect_short:=GetShortVector(eMatSec, CritNorm);
    Add(List_NewVectCand, NewVect_short);
    #
    NewVect_float:=EigenvalueFindNegativeVect(eMatSec);
    Add(List_NewVectCand, NewVect_float);
    #
    StrictIneq:=true;
    NeedNonZero:=true;
    NewVect_infinite:=SHORT_GetShortVector_InfinitePrecision(eMatSec, CritNorm, StrictIneq, NeedNonZero);
    Add(List_NewVectCand, NewVect_infinite);
    #
    List_NormL1:=List(List_NewVectCand, x->Norm_L1(x));
    TheMin:=Minimum(List_NormL1);
    pos:=Position(List_NormL1, TheMin);
    NewVect:=List_NewVectCand[pos];
    Print("EIG : NewVect=", NewVect, "\n");
    #
    return NewVect;
  fi;
end;


SHORT_ReduceBasisByFixingCommonValues:=function(ListVect, MatrixBasis)
  local n, nbMat, MatrixValues, MatrixValuesDiff, NSP, PreBasis, eNSP, eMat, i;
  n:=Length(ListVect[1]);
  nbMat:=Length(MatrixBasis);
  MatrixValues:=List(ListVect, x->List(MatrixBasis, y->x*y*x));
  MatrixValuesDiff:=List([2..Length(ListVect)], x->MatrixValues[x] - MatrixValues[1]);
  if Length(MatrixValuesDiff)>0 then
    NSP:=NullspaceMat(TransposedMat(MatrixValuesDiff));
  else
    NSP:=[];
  fi;
  PreBasis:=[];
  for eNSP in NSP
  do
    eMat:=NullMat(n,n);
    for i in [1..nbMat]
    do
      eMat:=eMat + eNSP[i]*MatrixBasis[i];
    od;
    Add(PreBasis, eMat);
  od;
  return PreBasis;
end;


SHORT_GetInitialSpanningSet:=function(ListVect)
  local n, ListVectTot, TheFamilyVect, eVect;
  n:=Length(ListVect[1]);
  ListVectTot:=Set(Concatenation(ListVect, -ListVect));
  TheFamilyVect:=[];
  for eVect in ListVect
  do
    Append(TheFamilyVect, List(IdentityMat(n), x->RemoveFraction(eVect+x)));
    Append(TheFamilyVect, List(IdentityMat(n), x->RemoveFraction(eVect-x)));
  od;
  return Difference(Set(TheFamilyVect), Union(ListVectTot, [ListWithIdenticalEntries(n,0)]));
end;


SHORT_TestRealizabilityShortestFamilyEquivariant:=function(ListVect, MatrixBasis, NoExtension, CaseComplex, TheMethod)
  local n, ListVectTot, ListDiff, TheBasis, TheFamilyVect, eVect, GetListIneq, ToBeMinimized, ListIneq, TheLP, ListNorm, SHV, NewSet, eMatFirst, eMatSec, i, j, DiffNew, SHVdiff, eVectBas, eEnt, nbMat, NewVect, NewVect_short, NewVect_float, NewVect_infinite, StrictIneq, NeedNonZero, eVectEmb, rVect, eScal1, eScal2, iVect, NSP, ListScal, DiagInfo, BasisToSymmetricMatrix, SymmetricMatrixToBasis, eVectTest, eSetIncd, eVertH, eExpr, eSymmEuct, eVertEuct, eVectEuct, ListScalEuct, ListVal, ePerm, ListValSort, DoLimitSize, eMaxVal, LimitSize, IdxSel, nbIter, ListMatSec, IdxKillSel, IdxKillNotSel, IdxKill, ListKillVect, eOptimal, eOptimalPrev, SetIneq, eVectPrimalDir, EllapsedTime, TotalEllapsedTime, TheDate1, TheDate2, CritTime, eList, MatrixValues, MatrixValuesDiff, eMat, eNSP, ListRay, ListRayTot, replyCone, TheFamilyCorr, SumIneq, ZerVect, CritNorm, HasOptimal, HasOptimalPrev, posZero, List_NormL1, TheMin, pos, List_NewVectCand, sizBas, PreBasis, SHORT_GetIneq, MinimalNormForeignVector;
  if CaseComplex<>"perfect" and CaseComplex<>"perfectcontain" and CaseComplex<>"centralcone" then
    Print("CaseComplex=", CaseComplex, " but allowed values are perfect, perfectcontain and centralcone\n");
    Error("please correct");
  fi;
  if CaseComplex="perfect" or CaseComplex="perfectcontain" then
    MinimalNormForeignVector:=1;
  else
    MinimalNormForeignVector:=2;
  fi;
  n:=Length(ListVect[1]);
  ListVectTot:=Set(Concatenation(ListVect, -ListVect));
  PreBasis:=SHORT_ReduceBasisByFixingCommonValues(ListVect, MatrixBasis);
  if CaseComplex="perfect" or CaseComplex="perfectcontain" then
    TheBasis:=PreBasis;
  else
    TheBasis:=GetIntegralValuedBasis(PreBasis);
  fi;
  sizBas:=Length(TheBasis);
  TheFamilyVect:=SHORT_GetInitialSpanningSet(ListVect);
  Print("|TheFamilyVect|=", Length(TheFamilyVect), "\n");
  SHORT_GetIneq:=function(x)
    if CaseComplex="perfect" or CaseComplex="perfectcontain" then
      return SHORT_GetIneq_Tspace(x,TheBasis);
    fi;
    return SHORT_GetIneq_Tspace_centralcone(x,TheBasis);
  end;
  GetListIneq:=function(TheFamVect)
    return List(TheFamVect, SHORT_GetIneq);
  end;
  ToBeMinimized:=[0];
  for eVectBas in TheBasis
  do
    Add(ToBeMinimized, ListVect[1]*eVectBas*ListVect[1]);
  od;
  if First(ToBeMinimized, x->x<>0)=fail then
    return rec(eCase:=1, reply:=false, replyContain:=false, TheFamilyVect:=TheFamilyVect);
  fi;
  BasisToSymmetricMatrix:=function(eVect)
    local eMatSec, i;
    eMatSec:=NullMat(n,n);
    for i in [1..sizBas]
    do
      eMatSec:=eMatSec + eVect[i]*TheBasis[i];
    od;
    return eMatSec;
  end;
  nbIter:=0;
  ListKillVect:=[];
  TotalEllapsedTime:=0;
  CritTime:=10;
  ZerVect:=SHORT_GetIneq(ListWithIdenticalEntries(n,0));
  HasOptimal:=false;
  HasOptimalPrev:=false;
  while(true)
  do
    if HasOptimalPrev and HasOptimal then
      if eOptimalPrev > eOptimal then
        Error("eOptimal should be increasing");
      fi;
    fi;
    if HasOptimal then
      HasOptimalPrev:=true;
      eOptimalPrev:=eOptimal;
    fi;
    nbIter:=nbIter+1;
    Print("nbIter=", nbIter, "\n");
    ListIneq:=GetListIneq(TheFamilyVect);
    if Length(Intersection(TheFamilyVect, ListVectTot))> 0 then
      Error("Intersection is non-empty. Cause of major bugs");
    fi;
    # not completely sure for line below.
    posZero:=Position(ListIneq, ZerVect);
    if posZero<>fail then
#      Print("posZero=", posZero, "\n");
#      Print("ListIneq=", ListIneq, "\n");
      return rec(eCase:=2, reply:=false, replyContain:=false, TheFamilyVect:=TheFamilyVect);
    fi;
    # Below is not needed by the above
    SetIneq:=Difference(Set(ListIneq), [ZerVect]);
    Print("|ListIneq|=", Length(ListIneq), " |SetIneq|=", Length(SetIneq), "\n");
    if Length(SetIneq)=0 then
      Error("Some bug to be solved");
    fi;
    TheDate1:=GetDate();
    if CaseComplex="perfect" or CaseComplex="perfectcontain" then
      if TheMethod = "cdd" then
        TheLP:=LinearProgramming(SetIneq, ToBeMinimized);
      fi;
      if TheMethod = "glpk_secure" then
        TheLP:=GLPK_LinearProgramming_Secure(SetIneq, ToBeMinimized);
      fi;
    else
      TheLP:=GLPK_IntegerLinearProgramming(SetIneq, ToBeMinimized);
    fi;
    TheDate2:=GetDate();
    EllapsedTime:=TheDate2 - TheDate1;
    TotalEllapsedTime:=TotalEllapsedTime + EllapsedTime;
    if IsBound(TheLP.dual_direction)=true then
      SumIneq:=ListWithIdenticalEntries(1+sizBas, 0);
      for eEnt in TheLP.dual_direction
      do
        Print("eEnt=", eEnt, "\n");
        Print("Before SumIneq=", SumIneq, "\n");
        SumIneq:=SumIneq + eEnt[2]*SetIneq[eEnt[1]];
        Print(" After SumIneq=", SumIneq, "\n");
        Print("     SetIneq[eEnt[1]]=", SetIneq[eEnt[1]], "\n");
      od;
      if SumIneq[1]<0 and SumIneq{[2..sizBas+1]}=ListWithIdenticalEntries(sizBas,0) then
        return rec(eCase:=3, reply:=false, replyContain:=false, TheFamilyVect:=TheFamilyVect);
      fi;
      Error("Need to solve here. Most likely a bug");
    elif IsBound(TheLP.primal_direction)=true then
      eVectPrimalDir:=ListWithIdenticalEntries(Length(TheBasis),0);
      for eEnt in TheLP.primal_direction
      do
        eVectPrimalDir[eEnt[1]]:=eEnt[2];
      od;
      AddSet(TheFamilyVect, 2*ListVect[1]);
    else
      if IsBound(TheLP.eVect)=false then
        Error("I think we have a real problem. Please debug");
      fi;
      eOptimal:=TheLP.optimal;
      HasOptimal:=true;
      Print("CaseComplex=", CaseComplex, "\n");
      if CaseComplex="perfect" or CaseComplex="perfectcontain" then
        Print("Selecting the perfect case\n");
        if eOptimal > 1 then
          # eOptimal is increasing so we finish here.
          return rec(eCase:=4, reply:=false, replyContain:=false, TheFamilyVect:=TheFamilyVect);
        fi;
        if NoExtension and eOptimal >= 1 then
          # when looking for simplicial configuration, we can already conclude here
          return rec(eCase:=5, reply:=false, replyContain:=false, TheFamilyVect:=TheFamilyVect);
        fi;
      else
        Print("Selecting the central cone case\n");
        if eOptimal > 2 then
	  # in central cone case this cannot happen.
          return rec(eCase:=6, reply:=false, replyContain:=false, TheFamilyVect:=TheFamilyVect);
	fi;
        if NoExtension and eOptimal >= 2 then
	  # in central cone case this cannot happen.
          return rec(eCase:=7, reply:=false, replyContain:=false, TheFamilyVect:=TheFamilyVect);
	fi;
      fi;
      eVectEmb:=TheLP.eVect;
      rVect:=TheLP.TheVert;
      if TheMethod<>"glpk_secure" then
        if CaseComplex="perfect" or CaseComplex="perfectcontain" then
          eSetIncd:=Filtered([1..Length(ListIneq)], x->ListIneq[x]*rVect=0);
          eVectTest:=Concatenation([ToBeMinimized[1]-TheLP.optimal],ToBeMinimized{[2..Length(ToBeMinimized)]});
          eExpr:=SolutionMatNonnegative(ListIneq{eSetIncd}, eVectTest);
          if eExpr=fail then
            Error("Error in the solutioning");
          fi;
        fi;
      fi;
      eMatSec:=BasisToSymmetricMatrix(eVectEmb);
      TheFamilyCorr:=TheFamilyVect{Filtered([1..Length(TheFamilyVect)], x->ListIneq[x]<>ZerVect)};
      ListNorm:=List(TheFamilyCorr, x->x*eMatSec*x);
      for iVect in [1..Length(TheFamilyVect)]
      do
        eScal1:=rVect*ListIneq[iVect]+MinimalNormForeignVector;
        eScal2:=TheFamilyVect[iVect]*eMatSec*TheFamilyVect[iVect];
        if eScal1<>eScal2 then
          Error("A few bugs remaining to be solved");
        fi;
      od;
      ListScal:=List(ListVect, x->x*eMatSec*x);
      if Length(Set(ListScal))<>1 then
        Error("Error in computation of norms");
      fi;
      CritNorm:=Minimum(1, ListScal[1]);
      if ListScal[1]<>TheLP.optimal then
        Error("Error in objective function value");
      fi;
      if Minimum(ListNorm)<1 then
        Error("We have a clear inconsistency in the code");
      fi;
      DiagInfo:=DiagonalizeSymmetricMatrix(eMatSec);
#      PrintArray(eMatSec);
      Print("   nbMinus=", DiagInfo.nbMinus, " nbPlus=", DiagInfo.nbPlus, " nbZero=", DiagInfo.nbZero, "\n");
      Print("   eOptimal=", eOptimal, "\n");
      if IsPositiveDefiniteSymmetricMatrix(eMatSec) then
        SHV:=ShortestVectorDutourVersion(eMatSec);
        Print("|SHV|=", Length(SHV), "\n");
        if Set(SHV)=ListVectTot then
          return rec(eCase:=8, reply:=true, eMat:=eMatSec, SHV:=ListVectTot, SHVclean:=SHORT_CleanAntipodality(ListVectTot), replyContain:=true, TheFamilyVect:=TheFamilyVect);
        else
          SHVdiff:=Difference(Set(SHV), ListVectTot);
          DiffNew:=Difference(SHVdiff, TheFamilyVect);
          if Length(DiffNew)>0 then
            TheFamilyVect:=Union(TheFamilyVect, DiffNew);
          else
            if IsSubset(Set(SHV), ListVectTot) then
              return rec(eCase:=9, reply:=false, eMat:=eMatSec, SHV:=SHV, SHVclean:=SHORT_CleanAntipodality(SHV), replyContain:=true, TheFamilyVect:=TheFamilyVect);
            else
              return rec(eCase:=10, reply:=false, replyContain:=false, TheFamilyVect:=TheFamilyVect);
            fi;
          fi;
        fi;
      else
        NewVect:=SHORT_GetShortZeroOrNegativeVector_General(eMatSec, CritNorm);
        if Position(ListVectTot, NewVect)<>fail then
          NewVect:=2*NewVect;
        fi;
        if Position(TheFamilyVect, NewVect)<>fail then
          Error("We have a very clear bug to resolve");
        fi;
        Add(TheFamilyVect, NewVect);
      fi;
    fi;
    Print("TotalEllapsedTime=", TotalEllapsedTime, "\n");
    if TotalEllapsedTime>CritTime and false then
      TotalEllapsedTime:=0;
      Print("Before ReductionLinearProgram\n");
      ListIneq:=GetListIneq(TheFamilyVect);
      eList:=ReductionLinearProgram(ListIneq, ToBeMinimized);
      Print("After ReductionLinearProgram\n");
      TheFamilyVect:=TheFamilyVect{eList};
    fi;
  od;
end;


KissingNumberUpperBound:=function(n)
  local ListVal;
  ListVal:=[2,6,12,24,45,78,135,240,366,554,870,1357,2069,3183,4866,7355];
  if n<=16 then
    return ListVal[n];
  fi;
  Error("Please write something here");
end;


SHORT_RankVectorFamily:=function(ListVect)
  local ListRankOne;
  ListRankOne:=List(ListVect, x->SymmetricMatrixToVector(TransposedMat([x]) * [x]));
  return RankMat(ListRankOne);
end;




#
# We use SHORT_GetIneq_Tspace to get the linear equality A[x] = 1.
# If for a family of vector v1, ....., vM and a vector w such that
# there exist coefficient a1, ...., aM such that
#     A[w] - 1 = sum ai (A[vi] - 1)    for all matrices A
# then if v1, ...., vM define a family of shortest vector then w is part of it.
# this is used for dimensionality extensions
SHORT_TestRealizabilityShortestFamily_General:=function(ListVectInput, CaseComplex, TheMethod)
  local n, StdBasis, ListVectWork, IsNeededInsert, FuncInsertVector, eVect, ListRankOneVector, InitialSize, eRecStab, MatrixBasis, RecTest, SizPrev, SizAfter, eO, fVect, replyRet, MatrGRP, NoExtension, ListRankOne, TheRank, ListIneq, nbIter, RecLLL, ListVect, SHVret, RetMat, TheTrans, InvTrans, SHVcleanRet;
  RecLLL:=SHORT_GetLLLreduction_Kernel(ListVectInput);
  ListVect:=RecLLL.SHVred;
  n:=Length(ListVect[1]);
  StdBasis:=GetStandardVoronoiSpace(n).Basis;
  if CaseComplex="perfect" then
    TheRank:=SHORT_RankVectorFamily(ListVect);
    NoExtension:=false;
    if Position([n, n+1, n+2], TheRank)<>fail then
      NoExtension:=true;
    fi;
  else
    NoExtension:=false;
  fi;
  ListVectWork:=[];
  FuncInsertVector:=function(eVect)
    if GetPositionAntipodal(ListVectWork, eVect)=fail then
      Add(ListVectWork, eVect);
    fi;
  end;
  for eVect in ListVect
  do
    FuncInsertVector(eVect);
  od;
  ListIneq:=List(ListVectWork, x->SHORT_GetIneq_Tspace(x, StdBasis));
  IsNeededInsert:=function(eVect)
    local eIneq, eSol;
    eIneq:=SHORT_GetIneq_Tspace(eVect, StdBasis);
    eSol:=SolutionMat(ListIneq, eIneq);
    if eSol=fail then
      return false;
    else
      return true;
    fi;
  end;
  InitialSize:=Length(ListVectWork);
  MatrGRP:=SHORT_GetStabilizer(ListVectWork).MatrGrp;
  Print("|Generators(MatrGRP)|=", Length(GeneratorsOfGroup(MatrGRP)), "\n");
  if CaseComplex="perfect" or CaseComplex="perfectcontain" then
    MatrixBasis:=InvariantFormDutourVersion(GeneratorsOfGroup(MatrGRP));
  else
    MatrixBasis:=GetStandardIntegralVoronoiSpace(n).Basis;
  fi;
  Print("CaseComplex=", CaseComplex, " : |MatrGRP|=", Order(MatrGRP), " |MatrixBasis|=", Length(MatrixBasis), "\n");
  nbIter:=0;
  while(true)
  do
    nbIter:=nbIter+1;
    if Length(ListVectWork) > KissingNumberUpperBound(n) then
      return rec(reply:=false, replyCone:=false, replyContain:=false);
    fi;
    Print("Before call with MatrixBasis\n");
    RecTest:=SHORT_TestRealizabilityShortestFamilyEquivariant(ListVectWork, MatrixBasis, NoExtension, CaseComplex, TheMethod);
#    Print("RecTest=", RecTest, "\n");
    Print(" After call with MatrixBasis\n");
    if RecTest.reply=true then
      replyRet:=Length(ListVectWork) = InitialSize;
      SHVret:=Concatenation(ListVectWork, -ListVectWork);
      TheTrans:=RecLLL.ReductionMatrix;
      InvTrans:=Inverse(TheTrans);
      RetMat:=TheTrans*RecTest.eMat*TransposedMat(TheTrans);
      return rec(reply:=replyRet, replyCone:=true, replyContain:=true, eMat:=RetMat, SHV:=SHVret*InvTrans, SHVclean:=ListVectWork*InvTrans);
    fi;
    if RecTest.replyContain=false then
      return rec(reply:=false, replyCone:=false, replyContain:=false);
    fi;
    SizPrev:=Length(ListVectWork);
    for eVect in RecTest.SHVclean
    do
      if IsNeededInsert(eVect) then
	eO:=Orbit(MatrGRP, eVect, OnPoints);
	for fVect in eO
	do
          FuncInsertVector(fVect);
	od;
      fi;
    od;
    SizAfter:=Length(ListVectWork);
    Print("nbIter=", nbIter, " SizPrev=", SizPrev, "  SizAfter=", SizAfter, "\n");
    if SizAfter=SizPrev then
      if RecTest.replyContain=false then
        return rec(reply:=false, replyCone:=false, replyContain:=false);
      else
        TheTrans:=RecLLL.ReductionMatrix;
        InvTrans:=Inverse(TheTrans);
        RetMat:=TheTrans*RecTest.eMat*TransposedMat(TheTrans);
        SHVret:=RecTest.SHVclean*InvTrans;
	SHVcleanRet:=Concatenation(SHVret, -SHVret);
        return rec(reply:=false, replyCone:=false, replyContain:=true, SHV:=SHVret, SHVclean:=SHVcleanRet, eMat:=RetMat);
      fi;
    fi;
  od;
end;




SHORT_TestRealizabilityShortestFamily:=function(ListVect)
  local TheMethod;
  TheMethod := "glpk_secure";
  return SHORT_TestRealizabilityShortestFamily_General(ListVect, "perfect", TheMethod);
end;

SHORT_TestRealizabilityShortestFamilyContain:=function(ListVect)
  local TheMethod;
  TheMethod := "glpk_secure";
  return SHORT_TestRealizabilityShortestFamily_General(ListVect, "perfectcontain", TheMethod);
end;


SHORT_TestRealizabilityCentralCone:=function(ListVect)
  return SHORT_TestRealizabilityShortestFamily_General(ListVect, "centralcone", "irrelevant");
end;


SHORT_GetGramFromPerfectConfiguration:=function(ListVect)
  local eMat;
  eMat:=SHORT_TestRealizabilityShortestFamily(ListVect).eMat;
  if Set(ShortestVectorDutourVersion(eMat))<>Set(Concatenation(ListVect, -ListVect)) then
    Error("There is a bug to solve");
  fi;
  return eMat;
end;



SHORT_GetKnownResults:=function(n, rank)
  local eDir, eFile, nSym, ListPerf, ListSHV, eMat, eSHV, nbSHV, eSHVred, i;
  nSym:=n*(n+1)/2;
  if rank > nSym then
    Print("rank=", rank, " nSym=", nSym, "\n");
    Error("rank should not be greater than nSym");
  fi;
  if rank < n then
    Print("rank=", rank, " n=", n, "\n");
    Error("rank should not be smaller than n");
  fi;
  if n=1 and rank=1 then
    eSHV:=[[1]];
    return [ eSHV ];
  fi;
  if nSym=rank then
    ListPerf:=GetAllPerfectForm(n);
    ListSHV:=[];
    for eMat in ListPerf
    do
      eSHV:=ShortestVectorDutourVersion(eMat);
      nbSHV:=Length(eSHV)/2;
      eSHVred:=[];
      for i in [1..nbSHV]
      do
        Add(eSHVred, eSHV[2*i]);
      od;
      Add(ListSHV, eSHVred);
    od;
    return ListSHV;
  fi;
  if n>11 then
    Error("Results are not known beyond dimension 11");
  fi;
  if n<=7 and n>3 then
    return GetConfigurationVectorFromPFPK(n, rank);
  fi;
  eDir:=DirectoriesPackageLibrary("MyPolyhedral", "DATA/ShortestVectors")[1];
  eFile:=Filename(eDir, Concatenation("ListSHV_n", String(n), "_rnk", String(rank)));
  if IsExistingFile(eFile)=false then
    Print("n=", n, "  rank=", rank, "\n");
    Error("We failed to find the right entry");
  fi;
  return ReadAsFunction(eFile)();
end;


SHORT_GetQuotientInvariant:=function(eSHV)
  local eMatRed, eDiag, eDiagFilt, CollDiagFilt;
  eMatRed:=BaseIntMat(eSHV);
  eDiag:=List([1..Length(eMatRed)], x->eMatRed[x][x]);
  eDiagFilt:=Filtered(eDiag, x->x<>1);
  CollDiagFilt:=Collected(eDiagFilt);
  return UndoCollected(CollDiagFilt);
end;



SHORT_IsInMatroidalLocus:=function(eSHV)
  local n, k, eSet, partSHV, eDet, NrComb, nbTest, eRec, eVect;
  k:=Length(eSHV[1]);
  n:=Length(eSHV);
  eVect:=[1..k];
  nbTest:=0;
  while(true)
  do
    nbTest:=nbTest+1;
    partSHV:=eSHV{eVect};
    eDet:=AbsInt(DeterminantMat(partSHV));
    if eDet<>0 and eDet<>1 then
      return false;
    fi;
    eRec:=BinomialStdvect_Increment(n,k,eVect);
    if eRec.test=false then
      break;
    fi;
    eVect:=eRec.eVect;
  od;
  NrComb:=NrCombinations([1..n],k);
  if NrComb<>nbTest then
    Print("We have NrComb=", NrComb, " nbTest=", nbTest, "\n");
    Error("Inconsistency");
  fi;
  return true;
end;


SHORT_IsIrreducibleVectorConfiguration:=function(SHV)
  local nbVect, n, eVect, eSet, fSet, eSHV, fSHV, eRnk, fRnk, eBasis, fBasis, TotBasis, eSHV_B, fSHV_B, nbTest, NrComb, eRec;
  nbVect:=Length(SHV);
  n:=Length(SHV[1]);
  eVect:=ListWithIdenticalEntries(nbVect,1);
  nbTest:=0;
  for eSet in Combinations([1..nbVect])
  do
    eSet:=Filtered([1..nbVect], x->eSet[x]=1);
    fSet:=Filtered([1..nbVect], x->eSet[x]=2);
    nbTest:=nbTest+1;
    eSHV:=SHV{eSet};
    fSHV:=SHV{fSet};
    eRnk:=PersoRankMat(eSHV);
    fRnk:=PersoRankMat(fSHV);
    if eRnk>0 and fRnk>0 and eRnk+fRnk=n then
      eSHV_B:=NullspaceIntMat(TransposedMat(eSHV));
      fSHV_B:=NullspaceIntMat(TransposedMat(fSHV));
      eBasis:=NullspaceIntMat(TransposedMat(eSHV_B));
      fBasis:=NullspaceIntMat(TransposedMat(fSHV_B));
      TotBasis:=Concatenation(eBasis, fBasis);
      if AbsInt(DeterminantMat(TotBasis))=1 then
        return false;
      fi;
    fi;
    eRec:=PowerSet_Increment(nbVect,2,eVect);
    if eRec.test=false then
      break;
    fi;
    eVect:=eRec.eVect;
  od;
  NrComb:=2^nbVect;
  if nbTest<>NrComb then
    Print("We have NrComb=", NrComb, " nbTest=", nbTest, "\n");
    Error("Critical error");
  fi;
  return true;
end;







SHORT_GetHigherDimensionFromKnownResults:=function(SHV)
  local n, ListRankOne, TheStab, rnk, ListSHV, ListRetTotal, TheCan, TheAct, eSHV, eListRankOne, RelStab, ListOrb, eOrb, fSHV, test, TheImg, O, ListRetOrbit, ListRetOrbitRed, ListOrbSize;
  n:=Length(SHV[1]);
  ListRankOne:=List(SHV, x->SymmetricMatrixToVector(TransposedMat([x])*[x]));
  TheStab:=SHORT_GetStabilizer(SHV);
  rnk:=RankMat(ListRankOne);
  Print("rnk=", rnk, "\n");
  ListSHV:=SHORT_GetKnownResults(n,rnk+1);
  ListRetTotal:=[];
  TheCan:=function(Vmat)
    return Set(List(Vmat, CanonicalizeVectForPerfect));
  end;
  TheAct:=function(x, g)
    return TheCan(x*g);
  end;
  for eSHV in ListSHV
  do
    eListRankOne:=List(eSHV, x->SymmetricMatrixToVector(TransposedMat([x])*[x]));
    RelStab:=SHORT_GetStabilizer(eSHV);
    ListOrb:=DualDescriptionStandard(eListRankOne, RelStab.PermGrpRed);
    for eOrb in ListOrb
    do
      fSHV:=eSHV{eOrb};
      if RankMat(fSHV)=n then
        test:=SHORT_TestEquivalence(fSHV, SHV);
        if test<>false then
          TheImg:=TheCan(eSHV*test.RetMat);
          Append(ListRetTotal, Orbit(TheStab.MatrGrp, TheImg, TheAct));
        fi;
      fi;
    od;
  od;
  O:=Orbits(TheStab.MatrGrp, ListRetTotal, TheAct);
  ListRetOrbit:=List(O, x->x[1]);
  ListRetOrbitRed:=List(ListRetOrbit, x->Difference(x, TheCan(SHV)));
  ListOrbSize:=List(O,Length);
  return rec(ListRetTotal:=ListRetTotal,
             ListOrbSize:=ListOrbSize, 
             ListRetOrbit:=ListRetOrbit,
             ListRetOrbitRed:=ListRetOrbitRed);
end;



SHORT_GetVertexEdgeColor:=function(eMat)
  local n, ListVertColor, eDiff, eMatRes, NSP, TotalBasis, ListSol, eDet, EdgeMatrix, ePair, i, j, ScalMatrix;
  n:=Length(eMat);
  ListVertColor:=[];
  ScalMatrix:=NullMat(n,n);
  for i in [1..n]
  do
    eDiff:=Difference([1..n], [i]);
    eMatRes:=eMat{eDiff};
    NSP:=NullspaceIntMat(TransposedMat(eMatRes));
    TotalBasis:=NullspaceIntMat(TransposedMat(NSP));
    ListSol:=List(eMatRes, x->SolutionMat(TotalBasis,x));
    eDet:=AbsInt(DeterminantMat(ListSol));
    Add(ListVertColor, eDet);
    ScalMatrix[i][i]:=eDet;
  od;
  EdgeMatrix:=NullMat(n,n);
  for ePair in Combinations([1..n],2)
  do
    i:=ePair[1];
    j:=ePair[2];
    eDiff:=Difference([1..n], ePair);
    eMatRes:=eMat{eDiff};
    NSP:=NullspaceIntMat(TransposedMat(eMatRes));
    TotalBasis:=NullspaceIntMat(TransposedMat(NSP));
    ListSol:=List(eMatRes, x->SolutionMat(TotalBasis,x));
    eDet:=AbsInt(DeterminantMat(ListSol));
    EdgeMatrix[i][j]:=eDet;
    EdgeMatrix[j][i]:=eDet;
    ScalMatrix[i][j]:=eDet;
    ScalMatrix[j][i]:=eDet;
  od;
  return rec(ListVertColor:=ListVertColor, EdgeMatrix:=EdgeMatrix, ScalMatrix:=ScalMatrix);
end;

SHORT_GetLevelInvariant:=function(eMat,k)
  local ListDet, n, eSet, eDiff, eMatRes, NSP, TotalBasis, ListSol, eDet;
  ListDet:=[];
  n:=Length(eMat);
  for eSet in Combinations([1..n],k)
  do
    eDiff:=Difference([1..n], eSet);
    eMatRes:=eMat{eDiff};
    NSP:=NullspaceIntMat(TransposedMat(eMatRes));
    TotalBasis:=NullspaceIntMat(TransposedMat(NSP));
    ListSol:=List(eMatRes, x->SolutionMat(TotalBasis,x));
    eDet:=AbsInt(DeterminantMat(ListSol));
    Add(ListDet, eDet);
  od;
  return Collected(ListDet);
end;



MapListGroupsToListIndex:=function(ListGroups)
  local eVect, iGroup, ePt;
  eVect:=[];
  for iGroup in [1..Length(ListGroups)]
  do
    for ePt in ListGroups[iGroup]
    do
      eVect[ePt]:=iGroup;
    od;
  od;
  return eVect;
end;



SHORT_ReduceByIsomorphism_info:=function(ListClasses)
  local ListInv, nbClass, ListStatus, iClass, jClass, test, eSet, eGroup, ListGroups, ListReduced;
  ListInv:=List(ListClasses, SHORT_Invariant);
  nbClass:=Length(ListClasses);
  ListStatus:=ListWithIdenticalEntries(nbClass,1);
  ListReduced:=[];
  ListGroups:=[];
  for iClass in [1..nbClass]
  do
    if ListStatus[iClass]=1 then
      Add(ListReduced, ListClasses[iClass]);
      eGroup:=[iClass];
      for jClass in [iClass+1..nbClass]
      do
        if ListStatus[jClass]=1 and ListInv[iClass]=ListInv[jClass] then
          test:=SHORT_TestEquivalence(ListClasses[iClass], ListClasses[jClass]);
          if test<>false then
            Add(eGroup, jClass);
            ListStatus[jClass]:=0;
          fi;
        fi;
      od;
      Add(ListGroups, eGroup);
    fi;
  od;
  return rec(ListReduced:=ListReduced, ListGroups:=ListGroups, ListIndex:=MapListGroupsToListIndex(ListGroups));
end;


SHORT_ReduceByIsomorphism_info_cpp:=function(ListClasses)
  local FileInput, FileOutput, output, eClass, TheCommand, U, nbGroup, ListGroups, i, nbEnt, iEnt, iGroup;
  FileInput:=Filename(POLYHEDRAL_tmpdir,"SHORT_Isomorphy.input");
  FileOutput:=Filename(POLYHEDRAL_tmpdir,"SHORT_Isomorphy.output");
  RemoveFileIfExist(FileInput);
  RemoveFileIfExist(FileOutput);
  output:=OutputTextFile(FileInput, true);
  AppendTo(output, Length(ListClasses), "\n");
  for eClass in ListClasses
  do
    CPP_WriteMatrix(output, eClass);
  od;
  CloseStream(output);
  #
  TheCommand:=Concatenation(FileShortReduceIsomorphyGAP, " ", FileInput, " ", FileOutput);
  Exec(TheCommand);
  #
  U:=ReadAsFunction(FileOutput)();
  nbGroup:=Length(U.ListReduced);
  ListGroups:=[];
  for i in [1..nbGroup]
  do
    Add(ListGroups, []);
  od;
  nbEnt:=Length(U.VectPos);
  for iEnt in [1..nbEnt]
  do
    iGroup:=U.VectPos[iEnt]+1;
    Add(ListGroups[iGroup], iEnt);
  od;
  return rec(ListReduced:=U.ListReduced, ListGroups:=ListGroups, ListIndex:=MapListGroupsToListIndex(ListGroups));
end;



SHORT_ReduceByIsomorphism:=function(ListClasses)
  return SHORT_ReduceByIsomorphism_info(ListClasses).ListReduced;
end;





SHORT_FindDifference:=function(ListClasses1, ListClasses2)
  local IsPresent, RetList, ListInv1, ListInv2, nbList1, nbList2, i1;
  ListInv1:=List(ListClasses1, SHORT_Invariant);
  ListInv2:=List(ListClasses2, SHORT_Invariant);
  nbList1:=Length(ListClasses1);
  nbList2:=Length(ListClasses2);
  IsPresent:=function(i1)
    local eInv1, i2, test;
    eInv1:=ListInv1[i1];
    for i2 in [1..nbList2]
    do
      if eInv1=ListInv2[i2] then
        test:=SHORT_TestEquivalence(ListClasses1[i1], ListClasses2[i2]);
        if test<>false then
          return true;
        fi;
      fi;
    od;
    return false;
  end;
  RetList:=[];
  for i1 in [1..nbList1]
  do
    if IsPresent(i1) then
      Add(RetList, ListClasses1[i1]);
    fi;
  od;
  return RetList;
end;







SHORT_KernelGetListDeterminantEqua:=function(eMatRes)
  local n, j, TestMat, k, l, eDet, eLine, eLineRed, uLine;
  n:=Length(eMatRes[1]);
  eLine:=[];
  for j in [1..n]
  do
    uLine:=ListWithIdenticalEntries(n,0);
    uLine[j]:=1;
    TestMat:=Concatenation(eMatRes, [uLine]);
    eDet:=DeterminantMat(TestMat);
    Add(eLine, eDet);
  od;
  return eLine;
end;

#
# Unfortunately, the code below cannot be used
# for the computation of quotient invariant.
# Sometimes we get [2,4] for one structure, 
# sometime [8] for another and yet they are isomorphic.
SHORT_GetQuotientList_V1:=function(eMat)
  local n, H, eList, eListB;
  n:=Length(eMat);
  H:=BaseIntMat(eMat);
  eList:=List([1..n], x->H[x][x]);
  eListB:=Filtered(eList, x->x<>1);
  return eListB;
end;


SHORT_GetQuotientList:=function(eMat)
  local ListFact;
  ListFact:=FactorsInt(AbsInt(DeterminantMat(eMat)));
  if ListFact = [1] then
    return [];
  fi;
  return ListFact;
end;


SHORT_Difference_Invariant:=function(eInvBig, eInvSma)
  local CollBig, CollSma, LSma, eInvuot, eEnt, eVal, pos, residualMult, h, eInvQuot, ListMatch;
  CollBig:=Collected(eInvBig);
  CollSma:=Collected(eInvSma);
  LSma:=List(CollSma, x->x[1]);
  ListMatch:=ListWithIdenticalEntries(Length(LSma),0);
  eInvQuot:=[];
  for eEnt in CollBig
  do
    eVal:=eEnt[1];
    pos:=Position(LSma, eVal);
    if pos=fail then
      residualMult:=eEnt[2];
    else
      residualMult:=eEnt[2] - CollSma[pos][2];
      ListMatch[pos]:=1;
    fi;
    if residualMult<0 then
      return fail;
    fi;
    if residualMult>0 then
      for h in [1..residualMult]
      do
        Add(eInvQuot, eVal);
      od;
    fi;
  od;
  if Position(ListMatch, 0)<>fail then
    return fail;
  fi;
  return eInvQuot;
end;


SHORT_KernelDetermineListPossibleDeterminant:=function(eMatRes, AllowedInvQuot)
  local n, i, ListListPosDet, eDiff, NSP, TotalBasis, ListSol, eInvSma, ListPosDet, eInvBig, CollDiff, LMult, eProd;
  n:=Length(eMatRes[1]);
  NSP:=NullspaceIntMat(TransposedMat(eMatRes));
  TotalBasis:=NullspaceIntMat(TransposedMat(NSP));
  ListSol:=List(eMatRes, x->SolutionMat(TotalBasis,x));
  eInvSma:=SHORT_GetQuotientList(ListSol);
  Print("  eInvSma=", eInvSma, "\n");
  if Product(eInvSma)<>AbsInt(DeterminantMat(ListSol)) then
    Error("Logical Inconsistency");
  fi;
  ListPosDet:=[0];
  for eInvBig in AllowedInvQuot
  do
    eDiff:=SHORT_Difference_Invariant(eInvBig, eInvSma);
    Print("    eInvBig=", eInvBig, " eInvSma=", eInvSma, " eDiff=", eDiff, "\n");
    if eDiff<>fail then
      if Length(eDiff)=0 then
        Append(ListPosDet, [-1,1]);
      else
        eProd:=Product(eDiff);
        Append(ListPosDet, [-eProd,eProd]);
      fi;
    fi;
  od;
  return rec(ListPosDet:=Set(ListPosDet), eInvSma:=eInvSma, ProdSma:=Product(eInvSma));
end;


SHORT_FullEnumerationPolytopeFAC:=function(eCase)
  local ListPosRhs, DetMat, n, nbSide, FAC, iSide, MinDet, MaxDet, eLine, fLine, j, ListISide, FACred;
  ListPosRhs:=eCase.ListListPosDet;
  DetMat:=eCase.MatrixDetEqua;
  n:=Length(eCase.eMat[1]);
  nbSide:=Length(ListPosRhs);
  Print("nbSide=", nbSide, "\n");
  FAC:=[];
  ListISide:=[];
  for iSide in [1..nbSide]
  do
#    Print("iSide=", iSide, " DetMat[iSide]=", DetMat[iSide], "\n");
    MinDet:=Minimum(ListPosRhs[iSide]);
    MaxDet:=Maximum(ListPosRhs[iSide]);
    if MinDet+MaxDet<>0 then
      Error("Some error somewhere");
    fi;
    eLine:=ListWithIdenticalEntries(n+1,0);
    fLine:=ListWithIdenticalEntries(n+1,0);
    eLine[1]:=MaxDet;
    fLine[1]:=MaxDet;
    for j in [1..n]
    do
      eLine[1+j]:= DetMat[iSide][j];
      fLine[1+j]:=-DetMat[iSide][j];
    od;
    Add(FAC, eLine);
    Add(FAC, fLine);
    Add(ListISide, iSide);
    Add(ListISide, iSide);
  od;
  Print("|FAC|=", Length(FAC), "\n");
  FACred:=List(FAC, x->x{[2..n+1]});
  return rec(FAC:=FAC, FACred:=FACred, nbFAC:=Length(FACred), ListISide:=ListISide);
end;





SHORT_FullEnumerationAllowedSolutionZsolve:=function(eCase)
  local ListPosRhs, DetMat, n, i, MinDet, MaxDet, eLine, fLine, j, TheResult, eDiff, O, ListRepr, eO, eRepr, ListPossSol, eSol, IsCorrect, iLine, ListVectTot, iSide, nbSide, FACredB, ListIntPoints, ListIntPointsExt, TheMethod, ListSiz, eGen, BigGen, eList, iFAC, eFAC, fFAC, eScal, pos1, pos2, ePermGen, eMatrGen, eVect, fVect, ePermGenRed, RecFAC, iSideImg, eSubset, eSubsetImg1, eSubsetImg2, SetListPossSol;
  n:=Length(eCase.eMat[1]);
  ListVectTot:=Set(Concatenation(eCase.eMat, -eCase.eMat));
  RecFAC:=SHORT_FullEnumerationPolytopeFAC(eCase);
  for ePermGen in GeneratorsOfGroup(eCase.eStab.PermGrp)
  do
    ePermGenRed:=Image(eCase.eStab.phiRed, ePermGen);
    eMatrGen:=Image(eCase.eStab.phi, ePermGen);
    BigGen:=FuncCreateBigMatrix(ListWithIdenticalEntries(n,0), eMatrGen);
    eList:=[];
    for iFAC in [1..RecFAC.nbFAC]
    do
      eFAC:=RecFAC.FAC[iFAC];
#      iSide:=RecFAC.ListISide[iFAC];
#      eSubset:=eCase.ListSubset[iSide];
#      eSubsetImg2:=OnSets(eSubset, ePermGenRed);
#      iSideImg:=Position(eCase.ListSubset, eSubsetImg2);
      eVect:=eFAC{[2..n+1]};
      fVect:=eVect*TransposedMat(eMatrGen);
      pos1:=Position(RecFAC.FACred, fVect);
      if pos1=fail then
        Error("Error for action on the facets 1");
      fi;
      fFAC:=eFAC*TransposedMat(BigGen);
      pos2:=Position(RecFAC.FAC, fFAC);
      if pos2=fail then
        Error("Error for action on the facets 2");
      fi;
      Add(eList, pos2);
    od;
    if PermList(eList)=fail then
      Error("Problem in construction of the permutation");
    fi;
  od;
#  TheMethod:="zsolve";
  TheMethod:="iteration";
  if TheMethod="zsolve" then
    ListIntPoints:=GetIntegralPointsZsolve(RecFAC.FAC);
  fi;
  if TheMethod="iteration" then
    ListIntPoints:=GetIntegralPointsIteration(RecFAC.FAC);
  fi;
  ListPossSol:=[];
  ListPosRhs:=eCase.ListListPosDet;
  DetMat:=eCase.MatrixDetEqua;
  nbSide:=Length(ListPosRhs);
  for eSol in ListIntPoints
  do
    for eFAC in RecFAC.FAC
    do
      eScal:=Concatenation([1], eSol) * eFAC;
      if eScal < 0 then
        Print("eSol=", eSol, " eFAC=", eFAC, "\n");
        Error("The point eSol is not in the polytope");
      fi;
    od;
    if eSol<>ListWithIdenticalEntries(n,0) and Position(ListVectTot, eSol)=fail then
      IsCorrect:=true;
      for iLine in [1..nbSide]
      do
        if Position(ListPosRhs[iLine], DetMat[iLine]*eSol)=fail then
          IsCorrect:=false;
        fi;
      od;
      if IsCorrect then
        Add(ListPossSol, eSol);
      fi;
    fi;
  od;
  Print("|ListPossSol|=", Length(ListPossSol), "\n");
  O:=Orbits(eCase.eStab.MatrGrp, ListPossSol, OnPoints);
  Print("|O|=", Length(O), "\n");
  ListRepr:=List(O, x->x[1]);
  ListSiz:=[];
  SetListPossSol:=Set(ListPossSol);
  for eRepr in ListRepr
  do
    eO:=Orbit(eCase.eStab.MatrGrp, eRepr, OnPoints);
    Add(ListSiz, Length(eO));
    if IsSubset(SetListPossSol, Set(eO))=false then
      Error("Critical code error");
    fi;
  od;
  Print("Coll(ListSiz)=", Collected(ListSiz), "\n");
  return ListRepr;
end;


SHORT_TestCorrectness:=function(eMat, eVect, TotalListPossMat, RecInv)
  local n, p, eMatB, testBySubspaces, i, eDiff, eMatCand, test, testReal, PostCheck, ListCand, eInv, IsPresent;
  n:=Length(eMat[1]);
  p:=Length(eMat);
  if Position(Concatenation(eMat, -eMat), eVect)<>fail then
    return false;
  fi;
  eMatB:=Concatenation(eMat, [eVect]);
  Print("eVect=", eVect, "\n");
  IsPresent:=function(testMat)
    local ListCandPos, ePos, test;
    ListCandPos:=RecInv.GetCandidates(testMat);
    for ePos in ListCandPos
    do
      test:=SHORT_TestEquivalence(testMat, TotalListPossMat[ePos]);
      if test<>false then
        return true;
      fi;
    od;
    return false;
  end;
  testBySubspaces:=true;
  if testBySubspaces then
    for i in [1..p]
    do
      eDiff:=Difference([1..p+1],[i]);
      eMatCand:=eMatB{eDiff};
      if RankMat(eMatCand)=n then
        if IsPresent(eMatCand)=false then
          return false;
	fi;
      fi;
    od;
  fi;
  testReal:=SHORT_TestRealizabilityShortestFamily(eMatB);
  Print("  reply=", testReal.reply, "\n");
  return testReal.reply;
end;


SHORT_GetECase:=function(eMat, AllowedInvQuot)
  local n, p, eStab, PreListListPosDet, PreMatrixDetEqua, ListDisc, eSet, eMatRes, eRecPosDet, RecRF, eLineFull, ListSubset, iSide, eDisc, ListListPosDet, MatrixDetEqua, len, ListListSubset, eListPosDet, SetDisc, pos, IsFirst, i, eListSubset, TheVect;
  n:=Length(eMat[1]);
  p:=Length(eMat);
  eStab:=SHORT_GetStabilizer(eMat);
  PreListListPosDet:=[];
  PreMatrixDetEqua:=[];
  ListSubset:=[];
  iSide:=0;
  Print("n=", n, " p=", p, "\n");
  ListDisc:=[];
  for eSet in Combinations([1..p],n-1)
  do
    Print("eSet=", eSet, "\n");
    eMatRes:=eMat{eSet};
    if RankMat(eMatRes)=n-1 then
      iSide:=iSide+1;
      Print("  Matching iSide=", iSide, "\n");
      eRecPosDet:=SHORT_KernelDetermineListPossibleDeterminant(eMatRes, AllowedInvQuot);
      Print("  ProdSma=", eRecPosDet.ProdSma, "  ListPosDet=", eRecPosDet.ListPosDet, "\n");
      eLineFull:=SHORT_KernelGetListDeterminantEqua(eMatRes);
      Print("  eLineFull=", eLineFull, "\n");
      RecRF:=RemoveFractionPlusCoef(eLineFull);
      Print("  RecRF.TheVect=", RecRF.TheVect, "\n");
      if eRecPosDet.ProdSma * RecRF.TheMult <> 1 then
        Print("eRecPosDet=", eRecPosDet.ProdSma, "\n");
	Print("RefRF.TheMult=", RecRF.TheMult, "\n");
        Error("Inconsistence in the reductions");
      fi;
      eDisc:=Set([RecRF.TheVect, -RecRF.TheVect]);
      Add(PreListListPosDet, eRecPosDet.ListPosDet);
      Add(PreMatrixDetEqua, RecRF.TheVect);
      Add(ListSubset, eSet);
      Add(ListDisc, eDisc);
    fi;
  od;
  len:=Length(ListDisc);
  Print("len=", len, "\n");
  SetDisc:=Set(ListDisc);
  Print("|SetDisc|=", Length(SetDisc), "\n");
  ListListPosDet:=[];
  MatrixDetEqua:=[];
  ListListSubset:=[];
  for eDisc in SetDisc
  do
    pos:=Position(ListDisc, eDisc);
    TheVect:=PreMatrixDetEqua[pos];
    eListSubset:=[];
    IsFirst:=true;
    for i in [1..len]
    do
      if ListDisc[i]=eDisc then
        Add(eListSubset, ListSubset[i]);
	if IsFirst then
	  eListPosDet:=PreListListPosDet[i];
	else
	  eListPosDet:=Intersection(eListPosDet, PreListListPosDet[i]);
	  IsFirst:=false;
	fi;
      fi;
    od;
    Add(ListListSubset, eListSubset);
    Add(MatrixDetEqua, TheVect);
    Add(ListListPosDet, eListPosDet);
  od;
  return rec(eMat:=eMat, 
             ListListPosDet:=ListListPosDet,
             MatrixDetEqua:=MatrixDetEqua,
             ListListSubset:=ListListSubset, 
             eStab:=eStab);
end;

RetrieveRecordInvariant:=function(ListObj, FuncInv)
  local ListInv, nbObj, SetInv, ListListMatch, ListMatch, i, eInv, GetCandidates;
  ListInv:=List(ListObj, FuncInv);
  nbObj:=Length(ListObj);
  SetInv:=Set(ListInv);
  ListListMatch:=[];
  for eInv in SetInv
  do
    ListMatch:=[];
    for i in [1..nbObj]
    do
      if ListInv[i]=eInv then
        Add(ListMatch, i);
      fi;
    od;
    Add(ListListMatch, ListMatch);
  od;
  GetCandidates:=function(eObj)
    local objInv, pos;
    objInv:=FuncInv(eObj);
    pos:=Position(SetInv, objInv);
    if pos=fail then
      return [];
    fi;
    return ListListMatch[pos];
  end;
  return rec(GetCandidates:=GetCandidates);
end;



SHORT_GetIsomorphyTypeFacets:=function(eMat, ListAllowedShortMat, ListAllowedStartMat, Prefix)
  local AllowedInvQuot, eStab, ListListPosDet, MatrixDetEqua, eCase, ListRepr, ListClasses, eRepr, test, eMatRepr, ListLen, NbCase, EstSize, iRepr, nbRepr, FileSave, RecInv;
  AllowedInvQuot:=Set(List(ListAllowedShortMat, SHORT_GetQuotientList));
#  Print("AllowedInvQuot=", AllowedInvQuot, "\n");
  eCase:=SHORT_GetECase(eMat, AllowedInvQuot);
  FileSave:=Concatenation(Prefix, "ZsolveSolutions");
  if IsExistingFilePlusTouch(FileSave) then
    ListRepr:=ReadAsFunction(FileSave)();
  else
    ListRepr:=SHORT_FullEnumerationAllowedSolutionZsolve(eCase);
    SaveDataToFilePlusTouch(FileSave, ListRepr);
  fi;
  ListClasses:=[];
  nbRepr:=Length(ListRepr);
  RecInv:=RetrieveRecordInvariant(ListAllowedStartMat, SHORT_Invariant);
  for iRepr in [1..nbRepr]
  do
    eRepr:=ListRepr[iRepr];
    Print("iRepr=", iRepr, "/", nbRepr, "\n");
    FileSave:=Concatenation(Prefix, "iRepr", String(iRepr));
    if IsExistingFilePlusTouch(FileSave) then
      test:=ReadAsFunction(FileSave)();
    else
      test:=SHORT_TestCorrectness(eMat, eRepr, ListAllowedStartMat, RecInv);
      SaveDataToFilePlusTouch(FileSave, test);
    fi;
    if test=true then
      eMatRepr:=Concatenation(eMat, [eRepr]);
      Add(ListClasses, eMatRepr);
    fi;
  od;
  Print("|ListClasses|=", Length(ListClasses), "\n");
  return ListClasses;
end;

SHORT_GetMaximumDeterminant:=function(SHV)
  local n, p, MaxDet, eSet, eDet;
  n:=Length(SHV[1]);
  p:=Length(SHV);
  MaxDet:=0;
  for eSet in Combinations([1..p], n)
  do
    eDet:=AbsInt(DeterminantMat(SHV{eSet}));
    if eDet>MaxDet then
      MaxDet:=eDet;
    fi;
  od;
  return MaxDet;
end;




SHORT_KernelSimplicialEnumeration:=function(ListMatrixStart, ListMatrixShort, SavePrefix)
  local n, nbStart, ListProd, TotalListClasses, ListIdxStartWork, ListIdxStartCons, ListAllowedStartMat, eIdx, FileSave, ListClassByIso, ListClassGen, eMat, MaxProd, eProd, NewPrefix, nbShort, ListShortProd, ListStartProd, ListIdxShortCons, ListAllowedShortMat, FileIndicate;
  n:=Length(ListMatrixShort[1][1]);
  nbStart:=Length(ListMatrixStart);
  nbShort:=Length(ListMatrixShort);
  Print("n=", n, " nbStart=", nbStart, " nbShort=", nbShort, "\n");
  ListShortProd:=List(ListMatrixShort, x->AbsInt(DeterminantMat(x)));
  MaxProd:=Maximum(ListShortProd);
  ListStartProd:=List(ListMatrixStart, SHORT_GetMaximumDeterminant);
  for eProd in Reversed([1..MaxProd])
  do
    ListIdxStartWork:=Filtered([1..nbStart], x->ListStartProd[x]=eProd);
    ListIdxStartCons:=Filtered([1..nbStart], x->ListStartProd[x]<=eProd);
    ListIdxShortCons:=Filtered([1..nbShort], x->ListShortProd[x]<=eProd);
    ListAllowedStartMat:=ListMatrixStart{ListIdxStartCons};
    ListAllowedShortMat:=ListMatrixShort{ListIdxShortCons};
    Print("eProd=", eProd, "\n");
    for eIdx in ListIdxStartWork
    do
      Print("  eIdx=", eIdx, " ListIdxStartWork=", ListIdxStartWork, "\n");
      FileSave:=Concatenation(SavePrefix, String(eIdx));
      FileIndicate:=Concatenation(SavePrefix, String(eIdx), "_Indicate");
      NewPrefix:=Concatenation(SavePrefix, "eIdx", String(eIdx), "_");
      if IsExistingFilePlusTouch(FileSave)=false and IsExistingFile(FileIndicate)=false then
        SaveDataToFile(FileIndicate, 0);
        eMat:=ListMatrixStart[eIdx];
        ListClassGen:=SHORT_GetIsomorphyTypeFacets(eMat, ListAllowedShortMat, ListAllowedStartMat, NewPrefix);
        SaveDataToFilePlusTouch(FileSave, ListClassGen);
        Print("    |ListClassGen|=", Length(ListClassGen), "\n");
      fi;
    od;
  od;
  TotalListClasses:=[];
  for eProd in Reversed([1..MaxProd])
  do
    ListIdxStartWork:=Filtered([1..nbStart], x->ListStartProd[x]=eProd);
    for eIdx in ListIdxStartWork
    do
      FileSave:=Concatenation(SavePrefix, String(eIdx));
      if IsExistingFilePlusTouch(FileSave)=false then
        Error("The full computation is not finished. Please rerun");
      fi;
      Append(TotalListClasses, ReadAsFunction(FileSave)());
    od;    
  od;
  Print("|TotalListClasses|=", Length(TotalListClasses), "\n");
  FileSave:=Concatenation(SavePrefix, "ByIso");
  if IsExistingFilePlusTouch(FileSave) then
    ListClassByIso:=ReadAsFunction(FileSave)();
  else
    ListClassByIso:=SHORT_ReduceByIsomorphism(TotalListClasses);
    SaveDataToFile(FileSave, ListClassByIso);
  fi;
  Print("|ListClassByIso|=", Length(ListClassByIso), "\n");
  return ListClassByIso;
end;

SHORT_FullEnumeration:=function(n, SavePrefix)
  local ListMatrix;
  ListMatrix:=List(SHORT_GetKnownResults(n, n), SHORT_GetLLLreduction);
  return SHORT_KernelSimplicialEnumeration(ListMatrix, ListMatrix, SavePrefix);
end;

SHORT_ExtensionByOneRank:=function(ListShortRankN, SavePrefix, Redo)
  local n, ListLowerRank, FuncInsertLowerRank, eShort, eStab, ListRay, LOrb, HaveLower, eOrb, eConf, FuncInsertUpperRank, ListUpperRank, iShort, eRecTest, GetAllContainingOrbits, iConf, nbConf, eLowerConf, NewUpperConf, ListOrbitConf, ListUpperInv, FileSave, eRec, ListGenerated, PartGen, GRPanti, eNewUpperConf, GetMatchingLowerConf, GetContaining_Strategy1, GetContaining_Strategy2, eRecConf;
  n:=Length(ListShortRankN[1][1]);
  GRPanti:=Group([-IdentityMat(n)]);
  nbConf:=Length(ListShortRankN);
  FuncInsertLowerRank:=function(eConf, TheUpper, iUpper)
    local len, i, test, TheUpperImg, eInv, ordStab, ordStabPair, OrbitSize;
    len:=Length(ListLowerRank);
    eInv:=SHORT_Invariant(eConf);
    ordStab:=Order(SHORT_GetStabilizer(eConf).PermGrp);
    ordStabPair:=Order(SHORT_GetStabilizerPair(eConf, TheUpper).PermGrp);
    OrbitSize:=ordStab/ordStabPair;
    for i in [1..len]
    do
      if ListLowerRank[i].eInv=eInv then
        test:=SHORT_TestEquivalence(eConf, ListLowerRank[i].eConf);
        if test<>false then
          TheUpperImg:=TheUpper*test.RetMat;
          if First(ListLowerRank[i].eConf, x->GetPositionAntipodal(TheUpperImg,x)=fail)<>fail then
            Error("Problem in TheUpperImg expression");
          fi;
          Add(ListLowerRank[i].ListOrbitCont, TheUpperImg);
          Add(ListLowerRank[i].ListIOrbitCont, iUpper);
          ListLowerRank[i].NbFacet:=ListLowerRank[i].NbFacet + OrbitSize;
          return;
        fi;
      fi;
    od;
    if First(eConf, x->GetPositionAntipodal(TheUpper,x)=fail)<>fail then
       Error("Problem in TheUpperImg expression");
    fi;
    Add(ListLowerRank, rec(eConf:=eConf, eInv:=eInv, ListOrbitCont:=[TheUpper], ListIOrbitCont:=[iUpper], NbFacet:=OrbitSize, ordStab:=ordStab));
  end;
  FileSave:=Concatenation(SavePrefix, "ListLowerRank");
  if IsExistingFilePlusTouch(FileSave) and Redo=false then
    ListLowerRank:=ReadAsFunction(FileSave)();
  else
    ListLowerRank:=[];
    for iConf in [1..nbConf]
    do
      Print("iConf=", iConf, "/", nbConf, "\n");
      eShort:=ListShortRankN[iConf];
      eStab:=SHORT_GetStabilizer(eShort);
      ListRay:=List(eShort, x->SymmetricMatrixToVector(TransposedMat([x])*[x]));
      LOrb:=DualDescriptionStandard(ListRay, eStab.PermGrpRed);
      for eOrb in LOrb
      do
        eConf:=eShort{eOrb};
        if RankMat(eConf)=n then
          FuncInsertLowerRank(eConf, eShort, iConf);
        fi;
      od;
    od;
    SaveDataToFilePlusTouch(FileSave, ListLowerRank);
  fi;
  Print("|ListLowerRank|=", Length(ListLowerRank), "\n");
  GetAllContainingOrbits:=function(LowerConf, TheConf)
    local eInv, eRec, test, eRecGRPrelevant, ListReturn, eOrbit, TheImg, eRecStab, eDCS, ePerm, eMatr, eRecStabLower, TheNew, TheNewExt, TheConfExt, LowerConfExt, TheUext, TheU, eConfExt;
    eInv:=SHORT_Invariant(LowerConf);
    eRecStabLower:=SHORT_GetStabilizer(LowerConf);
    TheConfExt:=Set(SHORT_GetAntipodals(TheConf));
    LowerConfExt:=Set(SHORT_GetAntipodals(LowerConf));
    for eRec in ListLowerRank
    do
      if eInv=eRec.eInv then
        test:=SHORT_TestEquivalence(eRec.eConf, LowerConf);
        if test<>false then
          eConfExt:=Set(SHORT_GetAntipodals(eRec.eConf*test.RetMat));
          if eConfExt<>LowerConfExt then
            Error("Error in RetMat");
          fi;
          eRecGRPrelevant:=SHORT_GetStabilizerPair(LowerConf, TheConf);
          ListReturn:=[];
          for eOrbit in eRec.ListOrbitCont
          do
            TheImg:=eOrbit*test.RetMat;
            if First(LowerConf, x->GetPositionAntipodal(TheImg,x)=fail)<>fail then
              Error("Problem in TheImg expression");
            fi;
            eRecStab:=SHORT_GetStabilizerPair(LowerConf, TheImg);
            for eDCS in DoubleCosets(eRecStabLower.PermGrp, eRecStab.PermGrp, eRecGRPrelevant.PermGrp)
            do
              ePerm:=Representative(eDCS);
              eMatr:=Image(eRecStabLower.phi, ePerm);
              TheNew:=TheImg*eMatr;
              TheNewExt:=Set(SHORT_GetAntipodals(TheNew));
              if Intersection(TheNewExt, TheConfExt)=LowerConfExt then
                TheUext:=Union(TheNewExt, TheConfExt);
                TheU:=List(Orbits(GRPanti, TheUext, OnPoints), x->x[1]);
                Add(ListReturn, TheU);
              fi;
            od;
          od;
          return ListReturn;
        fi;
      fi;
    od;
    Error("We should never reach that stage");
  end;
  GetMatchingLowerConf:=function(iUpper)
    local ListIOrbitMatch, len, IsFirst, i, iOrbit, NbFacet, ordStab, WeUpdate, Found_NbFacet, Found_ordStab, iOrbitSel, pos, TheUpper, TheUpperImg, test, eConf, eConfExt, TheUpperExt;
    ListIOrbitMatch:=Filtered([1..Length(ListLowerRank)], x->Position(ListLowerRank[x].ListIOrbitCont, iUpper)<>fail);
    len:=Length(ListIOrbitMatch);
    IsFirst:=true;
    for i in [1..len]
    do
      iOrbit:=ListIOrbitMatch[i];
      NbFacet:=ListLowerRank[iOrbit].NbFacet;
      ordStab:=ListLowerRank[iOrbit].ordStab;
      WeUpdate:=false;
      if IsFirst then
        WeUpdate:=true;
      else
        if NbFacet < Found_NbFacet then
          WeUpdate:=true;
        else
          if NbFacet = Found_NbFacet then
            if Found_ordStab > ordStab then
              WeUpdate:=true;
            fi;
          fi;
        fi;
      fi;
      IsFirst:=false;
      if WeUpdate then
        Found_NbFacet:=NbFacet;
        Found_ordStab:=ordStab;
        iOrbitSel:=iOrbit;
      fi;
    od;
    pos:=Position(ListLowerRank[iOrbitSel].ListIOrbitCont, iUpper);
    TheUpper:=ListShortRankN[iUpper];
    TheUpperImg:=ListLowerRank[iOrbitSel].ListOrbitCont[pos];
    test:=SHORT_TestEquivalence(TheUpperImg, TheUpper);
    if test=false then
      Error("Major bugs are left to solve");
    fi;
    eConf:=ListLowerRank[iOrbitSel].eConf*test.RetMat;
    eConfExt:=Set(SHORT_GetAntipodals(eConf));
    TheUpperExt:=Set(SHORT_GetAntipodals(TheUpper));
    if IsSubset(TheUpperExt, eConfExt)=false then
      Error("Major bugs are left to solve 2");
    fi;
    return rec(eLowerConf:=eConf, eConf:=ListShortRankN[iUpper], Found_NbFacet:=Found_NbFacet, Found_ordStab:=Found_ordStab, iOrbitSel:=iOrbitSel, iUpper:=iUpper);
  end;
  GetContaining_Strategy1:=function(eRecConf)
    local PartGen, eLowerConf, eConf, ListOrbitConf, eNewUpperConf, eRecTest;
    PartGen:=[];
    eLowerConf:=eRecConf.eLowerConf;
    eConf:=eRecConf.eConf;
    ListOrbitConf:=GetAllContainingOrbits(eLowerConf, eConf);
    Print("|ListOrbitConf|=", Length(ListOrbitConf), "\n");
    for eNewUpperConf in ListOrbitConf
    do
      eRecTest:=SHORT_TestRealizabilityShortestFamily(eNewUpperConf);
      if eRecTest.replyCone=true then
        if IsSubset(Set(eRecTest.SHV), Set(eNewUpperConf))=false then
          Error("We break one of the asked inclusions");
        fi;
        if RankMat(eRecTest.SHVclean)<>n then
          Error("The rank is not correct");
        fi;
        Add(PartGen, eRecTest.SHVclean);
      fi;
    od;
    return PartGen;
  end;
  GetContaining_Strategy2:=function(eRecConf)
    # Apparently, there is another strategy that I forgot about.
  end;
  for iShort in [1..nbConf]
  do
    Print("iShort=", iShort, "/", nbConf, "\n");
    FileSave:=Concatenation(SavePrefix, "ListGenerated_", String(iShort));
    if IsExistingFilePlusTouch(FileSave)=false or Redo then
      eRecConf:=GetMatchingLowerConf(iShort);
      PartGen:=GetContaining_Strategy1(eRecConf);
      SaveDataToFilePlusTouch(FileSave, PartGen);
    fi;
  od;
  ListGenerated:=[];
  for iShort in [1..nbConf]
  do
    Print("iShort=", iShort, "/", nbConf, "\n");
    FileSave:=Concatenation(SavePrefix, "ListGenerated_", String(iShort));
    PartGen:=ReadAsFunction(FileSave)();
    Append(ListGenerated, PartGen);
  od;
  Print("|ListGenerated|=", Length(ListGenerated), "\n");
  FileSave:=Concatenation(SavePrefix, "ByIso");
  if IsExistingFilePlusTouch(FileSave) and Redo=false then
    ListUpperRank:=ReadAsFunction(FileSave)();
  else
    ListUpperRank:=SHORT_ReduceByIsomorphism(ListGenerated);
    SaveDataToFilePlusTouch(FileSave, ListUpperRank);
  fi;
  Print("|ListUpperRank|=", Length(ListUpperRank), "\n");
  return ListUpperRank;
end;


SHORT_TestEquality:=function(SHV1, SHV2)
  local eVect1;
  if Length(SHV1)<>Length(SHV2) then
    return false;
  fi;
  for eVect1 in SHV1
  do
    if Position(SHV2, eVect1)=fail and Position(SHV2, -eVect1)=fail then
      return false;
    fi;
  od;
  return true;
end;


SHORT_IsOrientable:=function(eSHV)
  local ListRay, eSelect, eBasis, eRecGRP, eGen, TheMat, eEnt, fEnt, TheDet;
  ListRay:=List(eSHV, x->SymmetricMatrixToVector(TransposedMat([x])*[x]));
  eSelect:=RowReduction(ListRay).Select;
  eBasis:=ListRay{eSelect};
  eRecGRP:=SHORT_GetStabilizer(eSHV);
  for eGen in GeneratorsOfGroup(eRecGRP.PermGrpRed)
  do
    TheMat:=[];
    for eEnt in eSelect
    do
      fEnt:=OnPoints(eEnt, eGen);
      Add(TheMat, SolutionMat(eBasis, ListRay[fEnt]));
    od;
    TheDet:=DeterminantMat(TheMat);
    if AbsInt(TheDet)<>1 then
      Error("Wrong determinant");
    fi;
    if TheDet=-1 then
      return false;
    fi;
  od;
  return true;
end;


SHORT_CreateDifferential:=function(ListConfLow, ListConf)
  local nbConfLow, nbConf, n, ListInvLow, GetRecordOrientation, RecOriConf, RecOriConfLow, iConfOri, iConf, jConf, jConfOri, GetSelect, GetSignature, ListSelectLow, ListEntries, TheSign, TheDet, ListJConf, ListJVal, eConf, eSelect, ListRay, BasisCone, FuncInsert, SumRay, eRankOneExp, eRecSign, TheMatSqr, TheMat, eEntry, eConfLow, eVect, fVect, eSet, eVal, fSet;
  nbConfLow:=Length(ListConfLow);
  nbConf:=Length(ListConf);
  n:=Length(ListConf[1][1]);
  Print("n=", n, " nbConf=", nbConf, " nbConfLow=", nbConfLow, "\n");
  ListInvLow:=List(ListConfLow, SHORT_Invariant);
  GetRecordOrientation:=function(ListSHV)
    local nbSHV, ListOrientation, nbOri, ListIndexing, ListIndexingRev, i, j;
    nbSHV:=Length(ListSHV);
    ListOrientation:=List(ListSHV, SHORT_IsOrientable);
    nbOri:=Length(Filtered(ListOrientation, x->x=true));
    ListIndexing:=ListWithIdenticalEntries(nbSHV, 0);
    ListIndexingRev:=ListWithIdenticalEntries(nbOri, 0);
    j:=0;
    for i in [1..nbSHV]
    do
      if ListOrientation[i] then
        j:=j+1;
        ListIndexing[i]:=j;
        ListIndexingRev[j]:=i;
      fi;
    od;
    return rec(nbSHV:=nbSHV,
               nbOri:=nbOri,
               ListOrientation:=ListOrientation,
               ListIndexing:=ListIndexing,
               ListIndexingRev:=ListIndexingRev);
  end;
  RecOriConf:=GetRecordOrientation(ListConf);
  RecOriConfLow:=GetRecordOrientation(ListConfLow);
  GetSelect:=function(SHV)
    local ListRay;
    ListRay:=List(SHV, x->SymmetricMatrixToVector(TransposedMat([x])*[x]));
    return RowReduction(ListRay).Select;
  end;
  GetSignature:=function(eConfLow)
    local eInv, jConf, test, fConfLowImg;
    eInv:=SHORT_Invariant(eConfLow);
    for jConf in [1..nbConfLow]
    do
      if eInv=ListInvLow[jConf] then
        test:=SHORT_TestEquivalence(ListConfLow[jConf], eConfLow);
        if test<>false then
          fConfLowImg:=ListConfLow[jConf]*test.RetMat;
          if SHORT_TestEquality(fConfLowImg, eConfLow)=false then
	    Error("No equality when it should\n");
          fi;
          return rec(jConf:=jConf, eMat:=test.RetMat);
        fi;
      fi;
    od;
    Error("We should not reach that stage");
  end;
  ListSelectLow:=List(ListConfLow, GetSelect);
  ListEntries:=[];
  Print("RecOriConf.nbOri=", RecOriConf.nbOri, "  RecOriConfLow.nbOri=", RecOriConfLow.nbOri, "\n");
  for iConfOri in [1..RecOriConf.nbOri]
  do
    Print("iConfOri=", iConfOri, " / ", RecOriConf.nbOri, "\n");
    iConf:=RecOriConf.ListIndexingRev[iConfOri];
    eConf:=ListConf[iConf];
    eSelect:=GetSelect(eConf);
    ListRay:=List(eConf, x->SymmetricMatrixToVector(TransposedMat([x])*[x]));
    BasisCone:=ListRay{eSelect};
    ListJConf:=[];
    ListJVal:=[];
    FuncInsert:=function(jConf, eVal)
      local i;
      for i in [1..Length(ListJConf)]
      do
        if ListJConf[i]=jConf then
          ListJVal[i]:=ListJVal[i] + eVal;
          return;
        fi;
      od;
    end;
    SumRay:=Sum(ListRay);
    for eSet in DualDescriptionSets(ListRay)
    do
      eConfLow:=eConf{eSet};
      if RankMat(eConfLow)=n then
        eRecSign:=GetSignature(eConfLow);
        jConf:=eRecSign.jConf;
        jConfOri:=RecOriConfLow.ListIndexing[jConf];
        if jConfOri>0 then
          TheMat:=[SumRay];
          for eVal in ListSelectLow[jConf]
          do
            eVect:=ListConfLow[jConf][eVal];
            fVect:=eVect*eRecSign.eMat;
            if GetPositionAntipodal(eConf, fVect)=fail then
              Error("Failed to find position of fVect");
            fi;
            eRankOneExp:=SymmetricMatrixToVector(TransposedMat([fVect])*[fVect]);
            if Position(ListRay, eRankOneExp)=fail then
              Error("Error in equivalence somewhere. BUG");
            fi;
            Add(TheMat, eRankOneExp);
          od;
          TheMatSqr:=List(TheMat, x->SolutionMat(BasisCone, x));
          TheDet:=DeterminantMat(TheMatSqr);
          if TheDet > 0 then
            TheSign:=1;
          else
            TheSign:=-1;
          fi;
          FuncInsert(jConfOri, TheSign);
        fi;
      fi;
    od;
    fSet:=Filtered([1..Length(ListJVal)], x->ListJVal[x]<>0);
    eEntry:=rec(ListCol:=ListJConf{fSet}, ListVal:=ListJVal{fSet});
    Add(ListEntries, eEntry);
  od;
  return rec(nbLine:=RecOriConf.nbOri,
             nbCol:=RecOriConfLow.nbOri,
             ListEntries:=ListEntries);
end;


SHORT_TestEqualityFamilies:=function(ListSHV1, ListSHV2)
  local eSHV1, eSHV2, nbMatch, test, ListInv1, ListInv2, len1, len2, i1, i2;
  if Length(ListSHV1) <> Length(ListSHV2) then
    return false;
  fi;
  ListInv1:=List(ListSHV1, SHORT_Invariant);
  Print("We have ListInv1\n");
  ListInv2:=List(ListSHV2, SHORT_Invariant);
  Print("We have ListInv2\n");
  len1:=Length(ListSHV1);
  len2:=Length(ListSHV2);
  for i1 in [1..len1]
  do
    Print("i1=", i1, " / ", len1, "\n");
    eSHV1:=ListSHV1[i1];
    nbMatch:=0;
    for i2 in [1..len2]
    do
      eSHV2:=ListSHV2[i2];
      if ListInv1[i1]=ListInv2[i2] then
        test:=SHORT_TestEquivalence(eSHV1, eSHV2);
        if test<>false then
          nbMatch:=nbMatch+1;
        fi;
      fi;
    od;
    if nbMatch<>1 then
      return false;
    fi;
  od;
  return true;
end;


SHORT_GetPolytopeCyclicLattice:=function(n, MaxIndex)
  local FAC, eLine, i, fLine, gLine, uLow;
  FAC:=[];
  eLine:=ListWithIdenticalEntries(n+1,0);
  eLine[1]:=-1;
  eLine[2]:=1;
  Add(FAC, eLine);
  for i in [1..n-1]
  do
    fLine:=ListWithIdenticalEntries(n+1,0);
    fLine[i+1]:=-1;
    fLine[i+2]:=1;
    Add(FAC, fLine);
  od;
  uLow:=LowerInteger(MaxIndex/2);
  gLine:=ListWithIdenticalEntries(n+1,0);
  gLine[1]:=uLow;
  gLine[n+1]:=-1;
  Add(FAC, gLine);
  return FAC;
end;



IndexBoundWellRounded:=function(n)
  local MaxIndex, HermPower;
  HermPower:=GetHermitePower(n);
  MaxIndex:=1;
  while(true)
  do
    if MaxIndex^2<=HermPower and (MaxIndex+1)^2> HermPower then
      return MaxIndex;
    fi;
    MaxIndex:=MaxIndex+1;
  od;
end;



GetHextensionWellRounded:=function(eCand, hIdx)
  local n, ListCoset, eCoset, eList, NewMat, eLine, eTrans, i, ListCand;
  n:=Length(eCand);
  ListCoset:=GetMatrixCoset(eCand);
  ListCand:=[];
  for eCoset in ListCoset
  do
    for eList in BuildSet(n,[0..hIdx-1])
    do
      NewMat:=[];
      for eLine in eCand
      do
        Add(NewMat, Concatenation(eLine, [0]));
      od;
      eTrans:=eCoset;
      for i in [1..n]
      do
        eTrans:=eTrans + eList[i]*eCand[i];
      od;
      Add(NewMat, Concatenation(eTrans, [hIdx]));
      Add(ListCand, NewMat);
    od;
  od;
  Print("|ListCand|=", Length(ListCand), "\n");
  return ListCand;
end;



GetCandidatesWellRoundedNextDimension:=function(ListCandidatePrev, MaxIndex)
  local n, eCand, ListCand, ListCoset, eCoset, i, NewMat, eLine, hIdx, eDet;
  n:=Length(ListCandidatePrev[1][1]);
  ListCand:=[];
  Print("|ListCandidatePrev|=", Length(ListCandidatePrev), "\n");
  for eCand in ListCandidatePrev
  do
    eDet:=AbsInt(DeterminantMat(eCand));
    Print("eDet=", eDet, "\n");
    hIdx:=LowerInteger(MaxIndex/eDet);
    Append(ListCand, GetHextensionWellRounded(eCand, hIdx));
  od;
  return ListCand;
end;



TestCompatibilityWithSubseting:=function(EXT, ListPossibleTypeFaces)
  local len, i, eDiff, EXTface, NSP, TotalBasis, EXTfaceRed, test;
  len:=Length(EXT);
  for i in [1..len]
  do
    eDiff:=Difference([1..len],[i]);
    EXTface:=EXT{eDiff};
    NSP:=NullspaceIntMat(TransposedMat(EXTface));
    TotalBasis:=NullspaceIntMat(TransposedMat(NSP));
    EXTfaceRed:=List(EXTface, x->SolutionMat(TotalBasis,x));
    test:=First(ListPossibleTypeFaces, x->SHORT_TestEquivalence(x, EXTfaceRed)<>false);
    if test=fail then
      return false;
    fi;
  od;
  return true;
end;



CompleteLiftingWellRounded:=function(ListNonEquivRepr, MaxIndex)
  local ListCand, ListRepr, ListReprRef1, ListSolution, eRepr, test;
  ListCand:=GetCandidatesWellRoundedNextDimension(ListNonEquivRepr, MaxIndex);
  Print("|ListCand|=", Length(ListCand), "\n");
  ListRepr:=Filtered(ListCand, x->TestCompatibilityWithSubseting(x, ListNonEquivRepr)=true);
  Print("|ListRepr|=", Length(ListRepr), "\n");
  ListReprRef1:=SHORT_ReduceByIsomorphism(ListRepr);
  Print("|ListReprRef1|=", Length(ListReprRef1), "\n");
  ListSolution:=[];
  for eRepr in ListReprRef1
  do
    test:=SHORT_TestRealizabilityShortestFamily(eRepr);
    if test.reply=true then
      Add(ListSolution, eRepr);
    fi;
  od;
  Print("|ListSolution|=", Length(ListSolution), "\n");
  return ListSolution;
end;



SHORT_ExtensionByPrime:=function(SHVinp, pPrime)
  local GRPmatr, TheDim, ListOrb, NewListSHV, eOrb, eVect, NewBasis, BasisInv, SHVnew, eRecTest;
  GRPmatr:=SHORT_GetStabilizer(SHVinp).MatrGrp;
  TheDim:=Length(SHVinp[1]);
  ListOrb:=ComputeOrbitsVectors(GRPmatr, TheDim, pPrime);
  NewListSHV:=[];
  for eOrb in ListOrb
  do
    eVect:=eOrb.eVect;
    if eVect*eVect>0 then
      NewBasis:=SubspaceCompletion([eVect], Length(eVect));
      Add(NewBasis, eVect/pPrime);
      BasisInv:=Inverse(NewBasis);
      SHVnew:=SHVinp*BasisInv;
      eRecTest:=SHORT_TestRealizabilityShortestFamily(SHVnew);
      if eRecTest.reply then
        Add(NewListSHV, SHVnew);
      fi;
    fi;
  od;
  return NewListSHV;
end;




SHORT_ExtensionByPrime_GetCandidate:=function(SHVinp, pPrime)
  local GRPmatr, TheDim, ListOrb, ListCandSHV, eOrb, eVect, NewBasis, BasisInv, SHVnew;
  GRPmatr:=SHORT_GetStabilizer(SHVinp).MatrGrp;
  TheDim:=Length(SHVinp[1]);
  ListOrb:=ComputeOrbitsVectors(GRPmatr, TheDim, pPrime);
  ListCandSHV:=[];
  for eOrb in ListOrb
  do
    eVect:=eOrb.eVect;
    if eVect*eVect>0 then
      NewBasis:=SubspaceCompletion([eVect], Length(eVect));
      Add(NewBasis, eVect/pPrime);
      BasisInv:=Inverse(NewBasis);
      SHVnew:=SHVinp*BasisInv;
      Add(ListCandSHV, SHVnew);
    fi;
  od;
  return ListCandSHV;
end;


SHORT_GetCyclicPrimitive_Known:=function(n, pPrime)
  local eDir, eFile, ListSHV, ListReturn, eSHV;
  if IsPrime(pPrime)=false then
    Print("pPrime=", pPrime, "\n");
    Error("Should be prime");
  fi;
  if n<=9 then
    ListSHV:=SHORT_GetKnownResults(n, n);
    ListReturn:=[];
    for eSHV in ListSHV
    do
      if AbsInt(DeterminantMat(eSHV))=pPrime then
        Add(ListReturn, eSHV);
      fi;
    od;
    return ListReturn;
  fi;
  #
  eDir:=DirectoriesPackageLibrary("MyPolyhedral", "DATA/ShortestVectorsCyclicPrimitive")[1];
  eFile:=Filename(eDir, Concatenation("Cyclic_", String(n), "_", String(pPrime)));
  if IsExistingFile(eFile)=false then
    Print("n=", n, " pPrime=", pPrime, "\n");
    Print("eFile=", eFile, "\n");
    Error("eFile is missing");
  fi;
  return ReadAsFunction(eFile)();
end;



SHORT_GetCyclic_Known:=function(n, pPrime)
  local ListReturn, nCall, ListSHV, eSHV, eSHVbig, eLine, eLineBig, i;
  ListReturn:=[];
  for nCall in [5..n]
  do
    ListSHV:=SHORT_GetCyclicPrimitive_Known(nCall, pPrime);
    for eSHV in ListSHV
    do
      eSHVbig:=[];
      for eLine in eSHV
      do
        eLineBig:=Concatenation(eLine, ListWithIdenticalEntries(n-nCall, 0));
	Add(eSHVbig, eLineBig);
      od;
      for i in [nCall+1..n]
      do
        eLineBig:=ListWithIdenticalEntries(n, 0);
	eLineBig[i]:=1;
	Add(eSHVbig, eLineBig);
      od;
      Add(ListReturn, eSHVbig);
    od;
  od;
  return SHORT_ReduceByIsomorphism(ListReturn);
end;


SHORT_EnumerationConfiguration_MaxDet:=function(n, MaxDet)
  local ListComputed, GlobalExtensionByPrime, eDet, ListFact, eSmall, RedDet, ListSHV, eCase, TheListSHV;
  ListComputed:=[];
  Add(ListComputed, rec(det:=1, ListSHV:=[ IdentityMat(n) ]));
  GlobalExtensionByPrime:=function(ListSHVin, pPrime)
    local NewListSHV, eSHVin;
    NewListSHV:=[];
    for eSHVin in ListSHVin
    do
      Append(NewListSHV, SHORT_ExtensionByPrime(eSHVin, pPrime));
    od;
    return SHORT_ReduceByIsomorphism(NewListSHV);
  end;
  for eDet in [2..MaxDet]
  do
    Print("eDet=", eDet, "\n");
    if IsPrime(eDet) then
      TheListSHV:=SHORT_GetCyclic_Known(n, eDet);
    else
      ListFact:=Factors(eDet);
      eSmall:=Minimum(ListFact);
      RedDet:=eDet / eSmall;
      TheListSHV:=GlobalExtensionByPrime(ListComputed[RedDet].ListSHV, eSmall);
    fi;
    Add(ListComputed, rec(det:=eDet, ListSHV:=TheListSHV));
  od;
  ListSHV:=[];
  for eCase in ListComputed
  do
    Append(ListSHV, eCase.ListSHV);
  od;
  return ListSHV;
end;



SHORT_EnumerationConfiguration_MaxDet_PrimeSet:=function(n, MaxDet, ListPrime, SavePrefix)
  local ListComputed, GlobalExtensionByPrime, GlobalExtensionByPrime_Bis, eDet, ListFact, eSmall, RedDet, ListSHV, eCase, TheListSHV, FileSave;
  ListComputed:=[];
  Add(ListComputed, rec(det:=1, ListSHV:=[ IdentityMat(n) ]));
  GlobalExtensionByPrime:=function(ListSHVin, pPrime)
    local NewListSHV, eSHVin;
    NewListSHV:=[];
    for eSHVin in ListSHVin
    do
      Append(NewListSHV, SHORT_ExtensionByPrime(eSHVin, pPrime));
    od;
    return SHORT_ReduceByIsomorphism(NewListSHV);
  end;
  GlobalExtensionByPrime_Bis:=function(ListSHVin, pPrime, detTarget)
    local NewListSHV, NewListSHVred, eSHVin, FileSaveB, FileSaveC, nbCase, ListReturn, eSHV, iCase, eStatus;
    FileSaveB:=Concatenation(SavePrefix, "ListCandidates_", String(n), "_", String(detTarget));
    if IsExistingFilePlusTouch(FileSaveB)=false then
      NewListSHV:=[];
      for eSHVin in ListSHVin
      do
        Append(NewListSHV, SHORT_ExtensionByPrime_GetCandidate(eSHVin, pPrime));
      od;
      Print("|NewListSHV| = ", Length(NewListSHV), "\n");
      if IsInt(detTarget / (pPrime*pPrime)) and Length(NewListSHV) < 300000 then
        NewListSHVred:=SHORT_ReduceByIsomorphism(NewListSHV);
      else
        NewListSHVred:=NewListSHV;
      fi;
      SaveDataToFilePlusTouch(FileSaveB, NewListSHVred);
    else
      NewListSHVred:=ReadAsFunction(FileSaveB)();
    fi;
    nbCase:=Length(NewListSHVred);
    ListReturn:=[];
    for iCase in [1..nbCase]
    do
      Print("iCase=", iCase, "/", nbCase, "\n");
      FileSaveC:=Concatenation(SavePrefix, "Status_", String(n), "_", String(detTarget), "_", String(iCase));
      eSHV:=NewListSHVred[iCase];
      if IsExistingFilePlusTouch(FileSaveC) then
        eStatus:=ReadAsFunction(FileSaveC)();
      else
        eStatus:=SHORT_TestRealizabilityShortestFamily_General(eSHV, "perfect", "cdd").reply;
#        eStatus:=SHORT_TestRealizabilityShortestFamily(eSHV).reply;
        SaveDataToFilePlusTouch(FileSaveC, eStatus);
      fi;
      if eStatus then
        Add(ListReturn, eSHV);
      fi;
    od;
    return SHORT_ReduceByIsomorphism(ListReturn);
  end;
  for eDet in [2..MaxDet]
  do
    Print("eDet=", eDet, "\n");
    ListFact:=Factors(eDet);
    if IsSubset(Set(ListPrime), Set(ListFact)) then
      FileSave:=Concatenation(SavePrefix, "WellRoundedFixedDet_", String(n), "_", String(eDet));
      if IsExistingFilePlusTouch(FileSave) then
        TheListSHV:=ReadAsFunction(FileSave)();
      else
        if IsPrime(eDet) then
          TheListSHV:=SHORT_GetCyclic_Known(n, eDet);
        else
          eSmall:=Minimum(ListFact);
          RedDet:=eDet / eSmall;
#          TheListSHV:=GlobalExtensionByPrime(ListComputed[RedDet].ListSHV, eSmall);
          TheListSHV:=GlobalExtensionByPrime_Bis(ListComputed[RedDet].ListSHV, eSmall, eDet);
        fi;
        SaveDataToFilePlusTouch(FileSave, TheListSHV);
      fi;
    else
      TheListSHV:="unset";
    fi;
    Add(ListComputed, rec(det:=eDet, ListSHV:=TheListSHV));
  od;
  ListSHV:=[];
  for eCase in ListComputed
  do
    Append(ListSHV, eCase.ListSHV);
  od;
  return ListSHV;
end;




SHORT_GetKnownResultsIrreducible:=function(n, rank)
  return Filtered(SHORT_GetKnownResults(n,rank), SHORT_IsIrreducibleVectorConfiguration);
end;



SHORT_RankOneExtension:=function(eSHV)
  local n, fSHV, eVect;
  n:=Length(eSHV[1]);
  fSHV:=[];
  for eVect in eSHV
  do
    Add(fSHV, Concatenation(eVect,[0]));
  od;
  Add(fSHV, Concatenation(ListWithIdenticalEntries(n,0), [1]));
  return fSHV;
end;

SHORT_GetStrictlyReducedHulek:=function(n, rnk)
  local SHV1, SHVcorr1, SHV2, SHVext2, SHVfinal, eSHV, eFirst;
  SHV1:=SHORT_GetKnownResults(n, rnk);
  SHVcorr1:=Filtered(SHV1, x->SHORT_IsInMatroidalLocus(x)=false);
  SHV2:=SHORT_GetKnownResults(n-1, rnk-1);
  SHVext2:=List(SHV2, SHORT_RankOneExtension);
  SHVfinal:=[];
  for eSHV in SHVcorr1
  do
    eFirst:=First(SHVext2, x->SHORT_TestEquivalence(x, eSHV)<>false);
    if eFirst=fail then
      Add(SHVfinal, eSHV);
    fi;
  od;
  return SHVfinal;
end;


SHORT_NicePresentation:=function(output, eSHV)
  local nbVect, dim, ListRankOne, rnk, TheStab, TheOrder, ListGen, nbGen, iGen, eGen, eMatr;
  nbVect:=Length(eSHV);
  dim:=Length(eSHV[1]);
  ListRankOne:=List(eSHV, x->SymmetricMatrixToVector(TransposedMat([x])*[x]));
  rnk:=RankMat(ListRankOne);
  AppendTo(output, "Configuration of shortest vectors with ", nbVect, " vectors.\\\\\n");
  AppendTo(output, "Dimension is ", dim, " rank is ", rnk, ".\\\\\n");
  #
  AppendTo(output, "Representative is\n");
  LatexPrintMatrixEqua(output, eSHV);
  AppendTo(output, "Extended representative is\n");
  LatexPrintMatrixEqua(output, SHORT_GetAntipodals(eSHV));
  #
  TheStab:=SHORT_GetStabilizer(eSHV);
  TheOrder:=Order(TheStab.PermGrp);
  ListGen:=GeneratorsOfGroup(TheStab.PermGrp);
  nbGen:=Length(ListGen);
  AppendTo(output, "Size of integral automorphism group is ", TheOrder, ". Number of generators is ", nbGen, ".\n");
  #
  AppendTo(output, "\\begin{enumerate}\n");
  for iGen in [1..nbGen]
  do
    eGen:=ListGen[iGen];
    eMatr:=Image(TheStab.phi, eGen);
    AppendTo(output, "\\item Generator ", eGen, " with matrix representation\n");
    LatexPrintMatrixEqua(output, eMatr);
  od;
  AppendTo(output, "\\end{enumerate}\n");
end;






SHORT_PrimeFactorRefinement:=function(ListSHV, n, TheDet)
  local eFileIn, eFileOut, eFilePrime, ListPrime, outputPrime, nbPrime, ePrime, ListRec, i, nRel, ListCasesIrred, eCaseIrred, eCase, eFrame, eBasis, eSHV, eRecTest, eRec, nbRec, nbRecCorr, output, nbSHV, TheCommand, RefinedListSHV, eVal;
  eFileIn:=Filename(POLYHEDRAL_tmpdir,"PrimeFactIn");
  eFileOut:=Filename(POLYHEDRAL_tmpdir,"PrimeFactOut");
  eFilePrime:=Filename(POLYHEDRAL_tmpdir,"PrimeFact_Prime");
  
  ListPrime:=Set(FactorsInt(TheDet));
  outputPrime:=OutputTextFile(eFilePrime, true);
  nbPrime:=Length(ListPrime);
  AppendTo(outputPrime, n, "\n");
  AppendTo(outputPrime, nbPrime, "\n");
  for ePrime in ListPrime
  do
    ListRec:=[];
    for i in [0..n-1]
    do
      nRel:=n - i;
      ListCasesIrred:=SHORT_GetCandidateCyclic_Optimized(nRel,ePrime);
      for eCaseIrred in ListCasesIrred
      do
        eCase:=Concatenation(ListWithIdenticalEntries(i, 0), eCaseIrred);
        eFrame:=Concatenation(IdentityMat(n), [eCase / ePrime]);
        eBasis:=GetZbasis(eFrame);
        eSHV:=List(IdentityMat(n), x->SolutionMat(eBasis, x));
        eRecTest:=SHORT_TestRealizabilityShortestFamily_General(eSHV, "perfect", "glpk_secure");
        eRec:=rec(eCase:=eCase, eSHV:=eSHV, test:=eRecTest.reply);
        Add(ListRec, eRec);
      od;
    od;
    nbRec:=Length(ListRec);
    nbRecCorr:=Length(Filtered(ListRec, x->x.test));
    Print("ePrime=", ePrime, ", nbRec=", nbRec, " nbRecCorr=", nbRecCorr, "\n");
    AppendTo(outputPrime, ePrime, "\n");
    AppendTo(outputPrime, "1\n");
    AppendTo(outputPrime, nbRecCorr, "\n");
    for eRec in ListRec
    do
      if eRec.test then
        for eVal in eRec.eCase
        do
          AppendTo(outputPrime, " ", eVal);
        od;
        AppendTo(outputPrime, "\n");
      fi;
    od;
  od;
  CloseStream(outputPrime);
  #
  # Now eFileIN
  #
  output:=OutputTextFile(eFileIn, true);
  for eSHV in ListSHV
  do
    AppendTo(output, "1\n");
    CPP_WriteMatrix(output, eSHV);
  od;
  AppendTo(output, "0\n");
  CloseStream(output);
  Print("eFileIn created\n");
  #
  TheCommand:=Concatenation(FilePrimeRefinement, " ", eFilePrime, " ", eFileIn, " ", eFileOut);
  Print("TheCommand=", TheCommand, "\n");
  Exec(TheCommand);
  #
  RefinedListSHV:=ReadAsFunction(eFileOut)();
  RemoveFileIfExist(eFilePrime);
  RemoveFileIfExist(eFileIn);
  RemoveFileIfExist(eFileOut);
  return RefinedListSHV;
end;



#
# The method below does not work for case of dimension 6 and n=12 vectors.
# Correct number of unimodular vector systems is 125 but the method gives 124.
# Thus it is wrong.
#
SHORT_EnumerateTotallyUnimodular_attempt:=function(n, ThePrefix)
  local TheRank, ListConfig, ListPoss, FileSave, ListCandidate, ListMaximal, eConfig, FindExtension, ePoss, NewConfig, test;
  TheRank:=n;
  ListConfig:=[IdentityMat(n)];
  ListPoss:=BuildSet(n, [0,1]);
  while(true)
  do
    FileSave:=Concatenation(ThePrefix, "TotallyUnimodular_", String(n), "_", String(TheRank));
    SaveDataToFile(FileSave, ListConfig);
    Print("n=", n, " TheRank=", TheRank, " |ListConfig|=", Length(ListConfig), "\n");
    #
    ListCandidate:=[];
    ListMaximal:=[];
    for eConfig in ListConfig
    do
      FindExtension:=false;
      for ePoss in ListPoss
      do
        if Sum(ePoss) > 0 and Position(eConfig, ePoss)=fail then
          NewConfig:=Concatenation(eConfig, [ePoss]);
          test:=IsUnimodularVectorSystem(NewConfig);
          if test then
            FindExtension:=true;
            Add(ListCandidate, NewConfig);
          fi;
        fi;
      od;
      if FindExtension=false then
        Add(ListMaximal, eConfig);
      fi;
    od;
    Print("  |ListCandidate|=", Length(ListCandidate), "  |ListMaximal|=", Length(ListMaximal), "\n");
    #
    if Length(ListCandidate)=0 then
      break;
    fi;
    FileSave:=Concatenation(ThePrefix, "TotallyUnimodularMaximal_", String(n), "_", String(TheRank));
    SaveDataToFile(FileSave, ListMaximal);
    ListConfig:=SHORT_ReduceByIsomorphism(ListCandidate);
    Print("  |ListConfig|=", Length(ListConfig), "\n");
    TheRank:=TheRank+1;
  od;
end;




SHORT_GetIrreducibleRegularMatroids_V1:=function(n, rnk)
  local eDir, eFile, U, ConvertNumberToVector, nbOrbit, ListSHV, iOrbit, eLine, eVal, eVect, eSHV, dimSym;
  if n=2 then
    return [];
  fi;
  if n>7 and rnk>15 then
    Print("n=", n, " rnk=", rnk, "\n");
    Error("What is known is n<=7 or rank<=15");
  fi;
  if rnk=n+1 then
    return [GetCyclicComplex(n)];
  fi;
  if n>1 and n=rnk then
    return [];
  fi;
  dimSym:=n*(n+1)/2;
  if rnk > dimSym then
    Print("rnk=", rnk, " dimSym=", dimSym, "\n");
    Error("Maximal value allowed is dimSym");
  fi;
  eDir:=DirectoriesPackageLibrary("MyPolyhedral", "DATA/IrreducibleRegularMatroid_fripertinger")[1];
  eFile:=Filename(eDir, Concatenation("reg_simple_con", String(rnk), "_", String(n), ".txt"));
  U:=ReadVectorFile(eFile);
  ConvertNumberToVector:=function(eVal)
    local eVect, TheValue, i, ThePow, TwoPow, res;
    eVect:=ListWithIdenticalEntries(n,0);
    TheValue:=eVal;
    ThePow:=1;
    for i in [1..n]
    do
      TwoPow:=ThePow*2;
      res:=TheValue mod TwoPow;
      eVect[i]:=res/ThePow;
      TheValue:=TheValue - res;
      ThePow:=TwoPow;
    od;
    return eVect;
  end;
  nbOrbit:=U[4][1];
  ListSHV:=[];
  for iOrbit in [1..nbOrbit]
  do
    eLine:=U[iOrbit + 4];
    eSHV:=[];
    for eVal in eLine
    do
      eVect:=ConvertNumberToVector(eVal);
      Add(eSHV, eVect);
    od;
    Add(ListSHV, eSHV);
  od;
  return ListSHV;
end;



SHORT_GetRegularMatroidEmbedding_Kernel:=function(output, eMat)
  local nbLine, nbCol, iCol, iLine;
  nbLine:=Length(eMat);
  nbCol:=Length(eMat[1]);
  AppendTo(output, "M1 = Matrix(GF(2), [");
  for iCol in [1..nbCol]
  do
    if iCol>1 then
      AppendTo(output, ",");
    fi;
    AppendTo(output, "[");
    for iLine in [1..nbLine]
    do
      if iLine>1 then
        AppendTo(output, ",");
      fi;
      AppendTo(output, eMat[iLine][iCol]);
    od;
    AppendTo(output, "]");
  od;
  AppendTo(output, "])\n");
  AppendTo(output, "M2 = Matroid(matrix=M1)\n");
  AppendTo(output, "M3 = make_regular_matroid_from_matroid(M2)\n");
  AppendTo(output, "M4 = Matrix(M3)\n");
  AppendTo(output, "nbRow = M4.nrows()\n");
  AppendTo(output, "nbCol = M4.ncols()\n");
  AppendTo(output, "strRet=str(nbRow) + \" \" + str(nbCol) + \"\\n\"\n");
  AppendTo(output, "for iRow in range(nbRow):\n");
  AppendTo(output, "    for iCol in range(nbCol):\n");
  AppendTo(output, "        strRet += \" \"\n");
  AppendTo(output, "        strRet += str(M4[iRow,iCol])\n");
  AppendTo(output, "    if (iRow < nbRow-1):\n");
  AppendTo(output, "        strRet += \"\\n\"\n");
  AppendTo(output, "print strRet\n");
end;





SHORT_GetRegularMatroidEmbedding:=function(eMat)
  local nbLine, FileInput, FileOutput, output, TheCommand, TheEmbed, U;
  FileInput :=Filename(POLYHEDRAL_tmpdir,"BinaryMatroid.sage");
  FileOutput:=Filename(POLYHEDRAL_tmpdir,"RegularMatroid.output");
  RemoveFileIfExist(FileInput);
  RemoveFileIfExist(FileOutput);
  output:=OutputTextFile(FileInput, true);
  AppendTo(output, "from sage.matroids.utilities import make_regular_matroid_from_matroid\n");
  SHORT_GetRegularMatroidEmbedding_Kernel(output, eMat);
  CloseStream(output);
  TheCommand:=Concatenation("sage ", FileInput, " > ", FileOutput);
  Exec(TheCommand);
  U:=ReadVectorFile(FileOutput);
  RemoveFileIfExist(FileInput);
  RemoveFileIfExist(FileOutput);
  nbLine:=U[1][1];
  TheEmbed:=TransposedMat(U{[2..nbLine+1]});
  return TheEmbed;
end;


SHORT_GetRegularMatroidEmbedding_Family_Kernel:=function(ListMat)
  local nbLine, FileInput, FileOutput, output, TheCommand, TheEmbed, eMat, U, ListEmbed, nbMat, pos, iMat, nbCol;
  FileInput :=Filename(POLYHEDRAL_tmpdir,"BinaryMatroid.sage");
  FileOutput:=Filename(POLYHEDRAL_tmpdir,"RegularMatroid.output");
  RemoveFileIfExist(FileInput);
  RemoveFileIfExist(FileOutput);
  output:=OutputTextFile(FileInput, true);
  AppendTo(output, "from sage.matroids.utilities import make_regular_matroid_from_matroid\n");
  for eMat in ListMat
  do
    SHORT_GetRegularMatroidEmbedding_Kernel(output, eMat);
  od;
  CloseStream(output);
  Print("SAGE input file created\n");
  TheCommand:=Concatenation("sage ", FileInput, " > ", FileOutput);
  Exec(TheCommand);
  Print("SAGE program run finished\n");
  U:=ReadVectorFile(FileOutput);
  nbMat:=Length(ListMat);
  Print("nbMat=", nbMat, "\n");
  ListEmbed:=[];
  pos:=0;
  for iMat in [1..nbMat]
  do
    pos:=pos+1;
    nbLine:=U[pos][1];
    nbCol:=U[pos][2];
    TheEmbed:=TransposedMat(U{[pos+1..pos+nbLine]});
    Add(ListEmbed, TheEmbed);
    pos:=pos+nbLine;
  od;
  RemoveFileIfExist(FileInput);
  RemoveFileIfExist(FileOutput);
  return ListEmbed;
end;

SHORT_GetRegularMatroidEmbedding_Family:=function(ListMat)
  local eSize, nbMat, nbPart, ListReturn, iPart, eBegin, eEnd, eBlock;
  eSize:=1000;
  nbMat:=Length(ListMat);
  nbPart:=UpperInteger(nbMat / eSize) + 1;
  ListReturn:=[];
  for iPart in [1..nbPart]
  do
    eBegin:=1 + (iPart-1)*eSize;
    if eBegin <= nbMat then
      eEnd:=Minimum(iPart*eSize, nbMat);
      eBlock:=ListMat{[eBegin..eEnd]};
      if Length(eBlock)>0 then
        Append(ListReturn, SHORT_GetRegularMatroidEmbedding_Family_Kernel(eBlock));
      fi;
    fi;
  od;
  return ListReturn;
end;


SHORT_GetIrreducibleRegularMatroids_V2:=function(n, rnk)
  local ListSHV, eSHV, fSHV, RetListSHV, ListBad;
  Print("n=", n, " rnk=", rnk, "\n");
  ListSHV:=SHORT_GetIrreducibleRegularMatroids_V1(n, rnk);
  Print("|ListSHV|=", Length(ListSHV), "\n");
  RetListSHV:=[];
  ListBad:=[];
  for eSHV in ListSHV
  do
    if SHORT_IsInMatroidalLocus(eSHV) then
      Add(RetListSHV, eSHV);
    else
      Add(ListBad, eSHV);
    fi;
  od;
  Print("|RetListSHV|=", Length(RetListSHV), " |ListBad|=", Length(ListBad), "\n");
  Print("ListBad formed\n");
  Append(RetListSHV, SHORT_GetRegularMatroidEmbedding_Family(ListBad));
  return RetListSHV;
end;


SHORT_ExportPhilippeElbazVincent:=function(FileSave, ListSHV)
  local output, nbSHV, iSHV, eSHV, nbRow, nbCol;
  RemoveFileIfExist(FileSave);
  output:=OutputTextFile(FileSave, true);
  nbSHV:=Length(ListSHV);
  AppendTo(output, nbSHV, "\n");
  for iSHV in [1..nbSHV]
  do
    eSHV:=ListSHV[iSHV];
    nbRow:=Length(eSHV);
    nbCol:=Length(eSHV[1]);
    AppendTo(output, nbRow, " ", nbCol, "\n");
    WriteMatrix(output, eSHV);
  od;
  CloseStream(output);
end;


SHORT_GetRegularMatroids:=function(n,rnk)
  local eDir, eFile, ListSHV;
  eDir:=DirectoriesPackageLibrary("MyPolyhedral", "DATA/RegularMatroid")[1];
  eFile:=Filename(eDir, Concatenation("ListOrbitRM_", String(n), "_", String(rnk)));
  if IsExistingFile(eFile)=false then
    Print("Calling SHORT_GetRegularMatroids with n=", n, " rnk=", rnk, "\n");
    Print("But the file eFile=", eFile, " is missing\n");
    Print("Maybe just a little more computations are needed\n");
    Error("Please correct");
  fi;
  ListSHV:=ReadAsFunction(eFile)();
  return ListSHV;
end;




SHORT_GetIrreducibleRegularMatroids:=function(n, rnk)
  local eDir, eFile, ListSHV;
  if n<=7 then
    eDir:=DirectoriesPackageLibrary("MyPolyhedral", "DATA/RegularMatroid")[1];
    eFile:=Filename(eDir, Concatenation("ListOrbitRM_", String(n), "_", String(rnk)));
    ListSHV:=ReadAsFunction(eFile)();
    return Filtered(ListSHV, SHORT_IsIrreducibleVectorConfiguration);
  fi;
  if n=rnk then
    return [];
  fi;
  if rnk>15 then
    Print("rnk=", rnk, "\n");
    Error("Classification for rank higher than 15 is not known");
  fi;
  eDir:=DirectoriesPackageLibrary("MyPolyhedral", "DATA/IrreducibleRegularMatroid")[1];
  eFile:=Filename(eDir, Concatenation("IrrRegMat_", String(n), "_", String(rnk)));
  return ReadAsFunction(eFile)();
end;

SHORT_SingleMergeOperation:=function(PrefixIn, PrefixOut)
  local idx, eFile1, eFile2, eRead1, eRead2, ListConf, FileSave, nbConfIn, nbConfOut;
  idx:=0;
  nbConfIn:=0;
  nbConfOut:=0;
  while(true)
  do
    Print("PrefixIn=", PrefixIn, " idx=", idx, " nbConfIn=", nbConfIn, " nbConfOut=", nbConfOut, "\n");
    idx:=idx+1;
    eFile1:=Concatenation(PrefixIn, String(2*idx-1));
    eFile2:=Concatenation(PrefixIn, String(2*idx));
    if IsExistingFile(eFile1)=false then
      return idx-1;
    fi;
    eRead1:=ReadAsFunction(eFile1)();
    if IsExistingFile(eFile2)=false then
      eRead2:=[];
    else
      eRead2:=ReadAsFunction(eFile2)();
    fi;
    nbConfIn:=nbConfIn + Length(eRead1) + Length(eRead2);
    ListConf:=SHORT_ReduceByIsomorphism(Concatenation(eRead1, eRead2));
    nbConfOut:=nbConfOut + Length(ListConf);
    FileSave:=Concatenation(PrefixOut, String(idx));
    SaveDataToFile(FileSave, ListConf);
    if IsExistingFile(eFile2)=false then
      return idx;
    fi;
  od;
end;

SHORT_MergeFileFamilyIntoCppFile:=function(PrefixIn, FileOut)
  local idx, nbConf, U, nbFile, iFile, eFile, output, eConf;
  idx:=0;
  nbConf:=0;
  while(true)
  do
    Print("PrefixIn=", PrefixIn, " idx=", idx, " nbConf=", nbConf, "\n");
    idx:=idx+1;
    eFile:=Concatenation(PrefixIn, String(idx));
    if IsExistingFile(eFile)=false then
      break;
    fi;
    U:=ReadAsFunction(eFile)();
    nbConf:=nbConf + Length(U);
  od;
  nbFile:=idx-1;
  Print("SHORT_MergeFileFamilyIntoCppFile nbFile=", nbFile, " nbConf=", nbConf, "\n");
  output:=OutputTextFile(FileOut, true);
  AppendTo(output, nbConf, "\n");
  for iFile in [1..nbFile]
  do
    eFile:=Concatenation(PrefixIn, String(iFile));
    U:=ReadAsFunction(eFile)();
    for eConf in U
    do
      CPP_WriteMatrix(output, eConf);
    od;
  od;
  CloseStream(output);
end;


SHORT_MergeOperation:=function(PrefixIn, PrefixOut)
  local iLevel, WorkPrefixIn, WorkPrefixOut, nbIdx, eFile;
  iLevel:=0;
  while(true)
  do
    iLevel:=iLevel+1;
    WorkPrefixOut:=Concatenation(PrefixOut, "stage", String(iLevel), "_");
    if iLevel=1 then
      WorkPrefixIn:=PrefixIn;
    else
      WorkPrefixIn:=Concatenation(PrefixOut, "stage", String(iLevel-1), "_");
    fi;
    nbIdx:=SHORT_SingleMergeOperation(WorkPrefixIn, WorkPrefixOut);
    if nbIdx=1 then
      eFile:=Concatenation(WorkPrefixOut, "1");
      return ReadAsFunction(eFile)();
    fi;
  od;
end;

#
#
# How to work with perfect domains in the complex.
# With the Basis we can define the Ryshkov version
# (B1[x], ...., Bm[x]) and this works well.
# 
# The cone defined by (p(v1), ...., p(vm)) is the perfect cone
# Opgenorth is not relevant since it concerns the case of cones defined by
# a group.
# 
# The construction of perfect domains for tiling a 
# that we need to take direcly the intersection
# 
# 
# 
SHORT_CreateECaseForPolyhedralDecomposition:=function(ListVect)
  local n, ListRankOne, ListSymmVect, SuperMat, rnk, ListIdx, Basis, BasisVect, ListExtRays, eSymmVect, eSol, eSolRed, ListFacets, GlobInvarMat, InvariantBasis, SymmGrpGlob, ListMat, SymmGrpPtWs, GRPmat, ListMatrGens, TheAct, TotalListMat, eO, ListPermGenListRankOne, eMat, TheSet, eListA, eListB, eList, eMatrGen, nbVect, nbMat, InvariantBasisImg, ListMatrGenRed, TheMat, eGen, eStab, ListPermGen, GRPperm, ScalProdMat, iMat, jMat, eMatImg, eImg, fMat, eInv, phi;
  #
  # Dimension
  #
  n:=Length(ListVect[1]);
  ListRankOne:=List(ListVect, x->TransposedMat([x]) * [x]);
  if Length(Set(ListRankOne))<>Length(ListRankOne) then
    Print("|Set(ListRankOne)|=", Length(Set(ListRankOne)), "\n");
    Print("|ListRankOne|=", Length(ListRankOne), "\n");
    Error("There are duplication in ListRankOne");
  fi;
  ListSymmVect:=List(ListRankOne, SymmetricMatrixToVector);
  SuperMat:=Sum(ListRankOne);
  rnk:=RankMat(SuperMat);
  if rnk < n then
    Print("Rank is rnk=", rnk, " but dimension is n=", n, "\n");
    Error("Please correct rankwise");
  fi;
  ListIdx:=RowReduction(ListSymmVect).Select;
  Basis:=ListRankOne{ListIdx};
  BasisVect:=ListSymmVect{ListIdx};
  #
  # polytopal structure
  #
  ListExtRays:=[];
  for eSymmVect in ListSymmVect
  do
    eSol:=SolutionMat(BasisVect, eSymmVect);
    eSolRed:=RemoveFraction(eSol);
    Add(ListExtRays, eSolRed);
  od;
  ListFacets:=DualDescription(ListExtRays);
  #
  # group structure
  #
  GlobInvarMat:=SuperMat;
  InvariantBasis:=__ExtractInvariantZBasisShortVectorNoGroup(SuperMat);
  nbVect:=Length(InvariantBasis);
  ScalProdMat:=GetScalProdMatrix(Basis, SuperMat);
  #
  # Global group of symmetries. Pretty hard to get.
  #
  GRPmat:=ArithmeticAutomorphismMatrixFamily_Nauty([SuperMat], InvariantBasis);
#  Print("|GRPmat|=", Order(GRPmat), "\n");
  TheAct:=function(x, g)
    return g*x*TransposedMat(g);
  end;
  TotalListMat:=[];
  for eMat in ListRankOne
  do
    if Position(TotalListMat, eMat)=fail then
      eO:=Orbit(GRPmat, eMat, TheAct);
      Append(TotalListMat, eO);
    fi;
  od;
  nbMat:=Length(TotalListMat);
  TheSet:=Set(List(ListRankOne, x->Position(TotalListMat, x)));
#  Print("nbMat=", nbMat, " |TheSet|=", Length(TheSet), "\n");
  ListMatrGens:=GeneratorsOfGroup(GRPmat);
  ListPermGen:=[];
  for eMatrGen in ListMatrGens
  do
    eInv:=Inverse(eMatrGen);
    eListA:=List(TotalListMat, x->Position(TotalListMat, eInv*x*TransposedMat(eInv)));
    eListB:=List(InvariantBasis, x->Position(InvariantBasis, x*eMatrGen));
    eList:=Concatenation(eListA, List(eListB, x->nbMat + x));
#    Print("eMatrGen : eList=", eList, "\n");
    eGen:=PermList(eList);
    InvariantBasisImg:=List([1..nbVect], x->InvariantBasis[OnPoints(nbMat + x, eGen)-nbMat]);
    TheMat:=FindTransformation(InvariantBasis, InvariantBasisImg, ());
    if TheMat<>eMatrGen then
      Print("Wrong construction");
      Print(NullMat(5));
    fi;
    Add(ListPermGen, eGen);
  od;
  GRPperm:=Group(ListPermGen);
  phi:=GroupHomomorphismByImagesNC(GRPperm, GRPmat, ListPermGen, ListMatrGens);
#  Print("|GRPperm|=", Order(GRPperm), "\n");
  eStab:=Stabilizer(GRPperm, TheSet, OnSets);
#  Print("|eStab|=", Order(eStab), "\n");
  ListMatrGenRed:=[];
  for eGen in GeneratorsOfGroup(eStab)
  do
    InvariantBasisImg:=List([1..nbVect], x->InvariantBasis[OnPoints(nbMat + x, eGen)-nbMat]);
    TheMat:=FindTransformation(InvariantBasis, InvariantBasisImg, ());
    if TheMat<>Image(phi, eGen) then
      Print("Inconsistency\n");
      Print(NullMat(5));
    fi;
    for iMat in [1..nbMat]
    do
      jMat:=OnPoints(iMat, eGen);
      eMat:=TotalListMat[iMat];
      fMat:=TotalListMat[jMat];
      eInv:=Inverse(TheMat);
      eMatImg:=eInv * eMat * TransposedMat(eInv);
      if eMatImg<>fMat then
        Print("Inconsistency to resolve\n");
	Print(NullMat(5));
      fi;
    od;
    Add(ListMatrGenRed, TheMat);
  od;
  SymmGrpGlob:=Group(ListMatrGenRed);
#  Print("|SymmGrpGlob|=", Order(SymmGrpGlob), "\n");
  for eGen in GeneratorsOfGroup(SymmGrpGlob)
  do
    for eMat in ListRankOne
    do
      eImg:=eGen * eMat * TransposedMat(eGen);
      if Position(ListRankOne, eImg)=fail then
        Print(NullMat(5));
      fi;
    od;
  od;
  #
  # The pointwise stabilizer. Far easier to get
  #
  ListMat:=Concatenation([SuperMat], ListRankOne);
  SymmGrpPtWs:=ArithmeticAutomorphismMatrixFamily_Nauty(ListMat, InvariantBasis);
  #
  # Now returning the stuff
  #
  return rec(n:=n,
             Basis:=Basis,
             SuperMat:=SuperMat,
             ListExtRays:=ListExtRays,
             ListFacets:=ListFacets,
             GlobInvarMat:=GlobInvarMat,
             ShortestFunction:=ShortestVectorDutourVersion,
             ScalProdMatrix:=ScalProdMat,
             SymmGrpGlob:=SymmGrpGlob,
             SymmGrpPtWs:=SymmGrpPtWs);
end;







DoReadFrinakFormat_Version1:=function(eFile)
  local FileRead, TheCommand, ListMat;
  FileRead:=Filename(POLYHEDRAL_tmpdir,"FileOut");
  #
  TheCommand:=Concatenation(FileReadFrinakFiles, " ", eFile, " ", FileRead);
  Exec(TheCommand);
  #
  ListMat:=ReadAsFunction(FileRead)();
  RemoveFileIfExist(FileRead);
  return ListMat;
end;


DoReadFrinakFormat_Version2:=function(eFile)
  local FileRead, TheCommand, ListMat;
  FileRead:=Filename(POLYHEDRAL_tmpdir,"FileOut");
  #
  TheCommand:=Concatenation(FileReadFrinakFiles2, " ", eFile, " ", FileRead);
  Exec(TheCommand);
  #
  ListMat:=ReadAsFunction(FileRead)();
  RemoveFileIfExist(FileRead);
  return ListMat;
end;


FrinakMatrixConversion:=function(eMat)
  local eMatTr, dim, eMatTr_SelA, eMatTr_SelB, eMatTr_SelC, TheCan;
  eMatTr:=TransposedMat(eMat);
  dim:=Length(eMatTr[1]);
  eMatTr_SelA:=Set(Filtered(eMatTr, x->x<>ListWithIdenticalEntries(dim,0)));
  TheCan:=function(eV)
    local firstVal;
    firstVal:=First(eV, x->x<>0);
    if firstVal=fail then
      Error("logical problem");
    fi;
    if firstVal>0 then
      return eV;
    else
      return -eV;
    fi;
  end;
  eMatTr_SelB:=List(eMatTr_SelA, TheCan);
  eMatTr_SelC:=Set(eMatTr_SelB);
  return eMatTr_SelC;
end;


DoReadFrinakFormat_Version2_conversion:=function(eFile)
  local ListMat;
  ListMat:=DoReadFrinakFormat_Version2(eFile);
  return List(ListMat, FrinakMatrixConversion);
end;



GetFrinakVectorConfSignature:=function(eMatRed)
  local RecTest, val1, val2, val3;
  if eMatRed = [[1]] then
    RecTest:=rec(reply:=true, replyCone:=true, replyContain:=true);
  else
    RecTest:=SHORT_TestRealizabilityShortestFamily(eMatRed);
    if RecTest.replyCone=false then
      RecTest:=SHORT_TestRealizabilityShortestFamilyContain(eMatRed);
    fi;
  fi;
  if RecTest.reply then
    val1:=1;
  else
    val1:=0;
  fi;
  if RecTest.replyCone then
    val2:=1;
  else
    val2:=0;
  fi;
  if RecTest.replyContain then
    val3:=1;
  else
    val3:=0;
  fi;
  return rec(val1:=val1, val2:=val2, val3:=val3);
end;







SHORT_ComputationContainingCones_Direct:=function(SHV)
  local n, ListAdditionalVector, StdBasis, RelevantBasis, SHORT_GetIneq, dimSpace, MainLinForm, eStab, TheFamilyVect, ListIneq, eVect, eIneq, eIneqRed, ListIneqSet, ListPos, IsFinished, ListSets, ListPerfectMatrices, eSet, ListB, ListEqua, TotalMat, TotalMatFinal, lambda, recSHV, eVal, SHVtot, iMat, NewVect, eSol, CritNorm, SaturationOrbit, ListPart, ListPartGens, GRPpart, FuncInsert, ePart, eList, ePerm, eGen, GRPtot, eSetSelect, MinimallyFullDimensional, TheFamilyVect1, TheFamilyVect2, GetRepresentationOfGroup, TotRec, EliminateRedundantVector;
  n:=Length(SHV[1]);
  SHVtot:=Set(Concatenation(SHV, -SHV));
  ListAdditionalVector:=SHORT_GetInitialSpanningSet(SHV);
  StdBasis:=GetStandardVoronoiSpace(n).Basis;
  RelevantBasis:=SHORT_ReduceBasisByFixingCommonValues(SHV, StdBasis);
  SHORT_GetIneq:=function(eVect)
    local eIneq, eVectBas;
    eIneq:=[];
    for eVectBas in RelevantBasis
    do
      Add(eIneq, eVect*eVectBas*eVect);
    od;
    return eIneq;
  end;
  dimSpace:=Length(RelevantBasis);
  MainLinForm:=SHORT_GetIneq(SHV[1]);
  #
  eStab:=SHORT_GetStabilizer(SHV);
  Print("|eStab.MatrGrp|=", Order(eStab.MatrGrp), "\n");
  SaturationOrbit:=function(SHV)
    local nbSHV, ListStat, TheFamilyFinal, iSHV, eSHV, eO, eVal, pos;
    nbSHV:=Length(SHV);
    ListStat:=ListWithIdenticalEntries(nbSHV,1);
    TheFamilyFinal:=[];
    for iSHV in [1..nbSHV]
    do
      if ListStat[iSHV]=1 then
        eSHV:=SHV[iSHV];
        eO:=Orbit(eStab.MatrGrp, eSHV, OnPoints);
	Append(TheFamilyFinal, eO);
        for eVal in eO
        do
          pos:=Position(SHV, eVal);
          if pos<>fail then
            ListStat[pos]:=0;
          fi;
        od;
      fi;
    od;
    return TheFamilyFinal;
  end;
  MinimallyFullDimensional:=function(FamInput)
    local ListIneqPart, eVectPart, eIneqPart, eIneqPartRed, eSelectPart;
    ListIneqPart:=[];
    for eVectPart in FamInput
    do
      eIneqPart:=SHORT_GetIneq(eVectPart) - MainLinForm;
      eIneqPartRed:=RemoveFraction(eIneqPart);
      Add(ListIneqPart, eIneqPartRed);
    od;
    eSelectPart:=RowReduction(ListIneqPart).Select;
    return FamInput{eSelectPart};
  end;
  GetRepresentationOfGroup:=function(VectFamInput)
    local ListIneq, ListIneqSet, eVect, eIneq, eIneqRed, ListPart, ePart, ListPartGens, eGem, eList, ePerm, O, TheFamilyVectRepr, eO, iPart, eVectRepr;
    ListIneq:=[];
    for eVect in VectFamInput
    do
      eIneq:=SHORT_GetIneq(eVect) - MainLinForm;
      eIneqRed:=RemoveFraction(eIneq);
      Add(ListIneq, eIneqRed);
    od;
    ListIneqSet:=Set(ListIneq);
    ListPart:=[];
    for eIneq in ListIneqSet
    do
      ePart:=Filtered([1..Length(VectFamInput)], x->ListIneq[x]=eIneq);
      Add(ListPart, ePart);
    od;
    ListPartGens:=[];
    for eGen in GeneratorsOfGroup(eStab.MatrGrp)
    do
      eList:=List(ListPart, x->Position(ListPart, Set(List(x, y->Position(VectFamInput, VectFamInput[y]*eGen)))));
      ePerm:=PermList(eList);
      Add(ListPartGens, ePerm);
    od;
    GRPpart:=Group(ListPartGens);
    O:=Orbits(GRPpart, [1..Length(ListPart)], OnPoints);
    TheFamilyVectRepr:=[];
    for eO in O
    do
      iPart:=eO[1];
      ePart:=ListPart[iPart];
      eVectRepr:=VectFamInput[ePart[1]];
      Add(TheFamilyVectRepr, eVectRepr);
    od;
    Print("We have |ListIneq|=", Length(ListIneq), " |ListIneqSet|=", Length(ListIneqSet), " |GRPpart|=", Order(GRPpart), "\n");
    return rec(ListIneq:=ListIneq, ListIneqSet:=ListIneqSet, ListPart:=ListPart, GRPpart:=GRPpart, TheFamilyVectRepr:=TheFamilyVectRepr);
  end;
  EliminateRedundantVector:=function(TheFamInput)
    local LocRec, RecSelect, RetFamVect, eIdx;
    LocRec:=GetRepresentationOfGroup(TheFamInput);
    RecSelect:=EliminationByRedundancyEquivariant(LocRec.ListIneqSet, [], LocRec.GRPpart);
    Print("|eSetSelect|=", Length(RecSelect.eSetSelect), "\n");
    RetFamVect:=[];
    for eIdx in RecSelect.eSetSelect
    do
      Append(RetFamVect, TheFamInput{LocRec.ListPart[eIdx]});
    od;
    return RetFamVect;
  end;
  TheFamilyVect1:=SHORT_GetInitialSpanningSet(SHV);
  Print("We have |TheFamilyVect1|=", Length(TheFamilyVect1), "\n");
  TheFamilyVect2:=MinimallyFullDimensional(TheFamilyVect1);
  Print("We have |TheFamilyVect2|=", Length(TheFamilyVect2), "\n");
  TheFamilyVect:=SaturationOrbit(TheFamilyVect2);
#  TheFamilyVect:=TheFamilyVect2;
  Print("We have |TheFamilyVect|=", Length(TheFamilyVect), "\n");
  while(true)
  do
    Print("Start : |TheFamilyVect|=", Length(TheFamilyVect), "\n");
    TheFamilyVect:=EliminateRedundantVector(TheFamilyVect);
    Print("After reduction, |TheFamilyVect|=", Length(TheFamilyVect), "\n");
    TotRec:=GetRepresentationOfGroup(TheFamilyVect);
    #
    IsFinished:=true;
    FuncInsert:=function(aVect)
      local eO;
      if Position(TheFamilyVect, aVect)<>fail then
        return;
      fi;
      eO:=Orbit(eStab.MatrGrp, aVect, OnPoints);
      Append(TheFamilyVect, eO);
      IsFinished:=false;
    end;
    ListSets:=DualDescriptionStandard(TotRec.ListIneqSet, TotRec.GRPpart);
#    ListSets:=DualDescriptionSets(ListIneqSet);
    ListPerfectMatrices:=[];
    for eSet in ListSets
    do
      ListB:=[];
      ListEqua:=[];
      Add(ListB, 1);
      Add(ListEqua, MainLinForm);
      #
      for eVal in eSet
      do
        Add(ListB, 0);
        Add(ListEqua, TotRec.ListIneqSet[eVal]);
      od;
      eSol:=SolutionMat(TransposedMat(ListEqua), ListB);
      TotalMat:=NullMat(n,n);
      for iMat in [1..dimSpace]
      do
        TotalMat:=TotalMat + eSol[iMat]*RelevantBasis[iMat];
      od;
      TotalMatFinal:=RemoveFractionMatrix(TotalMat);
      Add(ListPerfectMatrices, TotalMatFinal);
      lambda:=SHV[1]*TotalMatFinal*SHV[1];
      if IsPositiveDefiniteSymmetricMatrix(TotalMatFinal) then
        recSHV:=ShortestVectors(TotalMatFinal, lambda-1);
        for eVect in recSHV.vectors
        do
          FuncInsert(eVect);
        od;
      else
        CritNorm:=lambda;
        NewVect:=SHORT_GetShortZeroOrNegativeVector_General(TotalMatFinal, CritNorm);
        FuncInsert(NewVect);
      fi;
    od;
    if IsFinished then
      break;
    fi;
  od;
  return rec(ListPerfectMatrices:=ListPerfectMatrices, TheFamilyVect:=TheFamilyVect, TheFamilyVectRepr:=TotRec.TheFamilyVectRepr);
end;


SHORT_ComputationContainingCones_Dictionary:=function(SHV)
  local n, eRank, RecStab, ListSHV, SHVtot, TheFamilyVect, TheFamilyVectRepr, GRPanti, FuncInsert, eOrbSHV, EXT, eLine, eProj, eProjVect, ListSets, eSet, eFacetSHV, test, eDiff, uVect;
  n:=Length(SHV[1]);
  eRank:=SHORT_Rank(SHV);
  RecStab:=SHORT_GetStabilizer(SHV);
  ListSHV:=SHORT_GetKnownResults(n, eRank+1);
  SHVtot:=Set(Concatenation(SHV, -SHV));
  TheFamilyVect:=[];
  TheFamilyVectRepr:=[];
  GRPanti:=Group([-IdentityMat(n)]);
  FuncInsert:=function(eVect)
    local eO, O, fO;
    eO:=Orbit(RecStab.MatrGrp, eVect, OnPoints);
    if Length(Intersection(Set(TheFamilyVect), Set(eO))) > 0 then
      return;
    fi;
    Add(TheFamilyVectRepr, eVect);
    O:=Orbits(GRPanti, eO, OnPoints);
    for fO in O
    do
      Add(TheFamilyVect, fO[1]);
    od;
    Print("Now |TheFamilyVect|=", Length(TheFamilyVect), " |TheFamilyVectRepr|=", Length(TheFamilyVectRepr), "\n");
  end;
  for eOrbSHV in ListSHV
  do
    EXT:=[];
    for eLine in eOrbSHV
    do
      eProj:=TransposedMat([eLine]) * [eLine];
      eProjVect:=SymmetricMatrixToVector(eProj);
      Add(EXT, eProjVect);
    od;
    ListSets:=DualDescriptionSets(EXT);
    for eSet in ListSets
    do
      eFacetSHV:=eOrbSHV{eSet};
      if RankMat(eFacetSHV)=n then
        test:=SHORT_TestEquivalence(eFacetSHV, SHV);
        if test<>false then
	  eOrbSHV:=eOrbSHV * test.RetMat;
	  eDiff:=Difference(Set(eOrbSHV), SHVtot);
          for uVect in eDiff
	  do
	    FuncInsert(uVect);
	  od;
        fi;
      fi;
    od;
  od;
  return rec(TheFamilyVect:=TheFamilyVect, TheFamilyVectRepr:=TheFamilyVectRepr);
end;



GetJarreSchmallowskyMatrix:=function(k1, k2)
  local n, eMat, i1, i2, j1, j2;
  n:=k1 + k2;
  eMat:=NullMat(n,n);
  for i1 in [1..k1]
  do
    for i2 in [1..k2]
    do
      j1:=i1;
      j2:=k1+i2;
      eMat[j1][j1]:=eMat[j1][j1]+1;
      eMat[j1][j2]:=eMat[j1][j2]+1;
      eMat[j2][j1]:=eMat[j2][j1]+1;
      eMat[j2][j2]:=eMat[j2][j2]+1;
    od;
  od;
  return eMat;
end;

SHORT_GetL1NormConfiguration:=function(eSHV)
  local eNorm, eVect, eVal;
  eNorm:=0;
  for eVect in eSHV
  do
    for eVal in eVect
    do
      eNorm:=eNorm + AbsInt(eVal);
    od;
  od;
  return eNorm;
end;

SHORT_GetStringFromVectorConfiguration:=function(eSHV)
  local eStrConf, iVect, preVect, eNNZ, eNNeg, eVect, n, eStrLine, IsFirst, i, eStrComp;
  eStrConf:="";
  for iVect in [1..Length(eSHV)]
  do
    preVect:=eSHV[iVect];
    eNNZ:=Length(Filtered(preVect, x->x<>0));
    eNNeg:=Length(Filtered(preVect, x->x<0));
    if eNNeg = eNNZ then
      eVect:=-preVect;
    else
      eVect:= preVect;
    fi;
    n:=Length(eVect);
    eStrLine:="\$";
    IsFirst:=true;
    for i in [1..n]
    do
      eStrComp:=Concatenation("e_{", String(i), "}");
      if eVect[i]>0 then
        if IsFirst then
          IsFirst:=false;
        else
          eStrLine:=Concatenation(eStrLine, "+");
        fi;
        if eVect[i]=1 then
          eStrLine:=Concatenation(eStrLine, eStrComp);
        else
          eStrLine:=Concatenation(eStrLine, String(eVect[i]), eStrComp);
        fi;
      fi;
    od;
    for i in [1..n]
    do
      eStrComp:=Concatenation("e_{", String(i), "}");
      if eVect[i]<0 then
        eStrLine:=Concatenation(eStrLine, "-");
        if eVect[i]=-1 then
          eStrLine:=Concatenation(eStrLine, eStrComp);
        else
          eStrLine:=Concatenation(eStrLine, String(-eVect[i]), eStrComp);
        fi;
      fi;
    od;
    eStrLine:=Concatenation(eStrLine, "\$");
    if iVect>1 then
      eStrConf:=Concatenation(eStrConf, ", ");
    fi;
    eStrConf:=Concatenation(eStrConf, eStrLine);
  od;
  return eStrConf;
end;

SHORT_GetSubconfigurations:=function(ListVect)
  local n, nbSHV, ListListVect, i, eDiff, ListVectSel, TheOrth, eBasis, eListVect, eVect, eSol;
  n:=Length(ListVect[1]);
  nbSHV:=Length(ListVect);
  ListListVect:=[];
  for i in [1..nbSHV]
  do
    eDiff:=Difference([1..nbSHV], [i]);
    ListVectSel:=ListVect{eDiff};
    if RankMat(ListVectSel)=n-1 then
      TheOrth:=NullspaceIntMat(TransposedMat(ListVectSel));
      eBasis:=NullspaceIntMat(TransposedMat(TheOrth));
      eListVect:=[];
      for eVect in ListVectSel
      do
        eSol:=SolutionIntMat(eBasis, eVect);
        Add(eListVect, eSol);
      od;
      Add(ListListVect, eListVect);
    fi;
  od;
  return ListListVect;
end;



