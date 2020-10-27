SYMPL_GetQuadruple:=function(TheMat)
  local g, A, B, C, D;
  g:=Length(TheMat)/2;
  A:=List(TheMat{[1..g]}, x->x{[1..g]});
  B:=List(TheMat{[1..g]}, x->x{[g+1..2*g]});
  C:=List(TheMat{[g+1..2*g]}, x->x{[1..g]});
  D:=List(TheMat{[g+1..2*g]}, x->x{[g+1..2*g]});
  return rec(A:=A, B:=B, C:=C, D:=D);
end;


SYMPL_GetEvenPairs:=function(g)
  local ListEven, eVect, fVect, eScal, eRes;
  ListEven:=[];
  for eVect in BuildSet(g, [0,1])
  do
    for fVect in BuildSet(g, [0,1])
    do
      eScal:=eVect*fVect;
      eRes:=eScal mod 2;
      if eRes=0 then
        Add(ListEven, [eVect, fVect]);
      fi;
    od;
  od;
  return ListEven;
end;

SYMPL_CreateElement:=function(A, B, C, D)
  local g, RetMat, i;
  g:=Length(A);
  RetMat:=[];
  for i in [1..g]
  do
    Add(RetMat, Concatenation(A[i], B[i]));
  od;
  for i in [1..g]
  do
    Add(RetMat, Concatenation(C[i], D[i]));
  od;
  return RetMat;
end;

SYMPL_EvenPairAction:=function(eEven, TheMat)
  local TheQuad, g, lVect1, lVect2, mVect1, mVect2, TheProd1, TheProd2, TheDiag1, TheDiag2, lVect2Red, mVect2Red;
  TheQuad:=SYMPL_GetQuadruple(TheMat);
  g:=Length(TheMat)/2;
  lVect1:=eEven[1];
  mVect1:=eEven[2];
  TheProd1:=TransposedMat(TheQuad.A)*TheQuad.C;
  TheDiag1:=List([1..g], x->TheProd1[x][x]);
  TheProd2:=TransposedMat(TheQuad.B)*TheQuad.D;
  TheDiag2:=List([1..g], x->TheProd2[x][x]);
  lVect2:=lVect1*TheQuad.A+mVect1*TheQuad.C+TheDiag1;
  mVect2:=lVect1*TheQuad.B+mVect1*TheQuad.D+TheDiag2;
  lVect2Red:=lVect2 mod 2;
  mVect2Red:=mVect2 mod 2;
  return [lVect2Red, mVect2Red]; 
end;






SYMPL_IsInModularGroup:=function(TheMat)
  local g, TheQuad, A, B, C, D, TheExpr;
  if IsIntegralMat(TheMat)=false then
    return false;
  fi;
  g:=Length(TheMat)/2;
  TheQuad:=SYMPL_GetQuadruple(TheMat);
  A:=TheQuad.A;
  B:=TheQuad.B;
  C:=TheQuad.C;
  D:=TheQuad.D;
  if TransposedMat(A)*C<>TransposedMat(C)*A then
    return false;
  fi;
  if TransposedMat(B)*D<>TransposedMat(D)*B then
    return false;
  fi;
  TheExpr:=TransposedMat(A)*D-TransposedMat(C)*B;
  if TheExpr<>IdentityMat(g) then
    return false;
  fi;
  return true;
end;

SYMPL_GetGenerators_Fractional:=function(g, eFrac)
  local ListGen, ZerMat, IdMat, HMat, HMat2, i, SMat;
  ListGen:=[];
  ZerMat:=NullMat(g,g);
  IdMat:=IdentityMat(g);
  Add(ListGen, SYMPL_CreateElement(ZerMat, IdMat, -IdMat, ZerMat));
  HMat:=NullMat(g,g);
  for i in [1..g]
  do
    HMat[i][NextIdx(g,i)]:=eFrac;
  od;
  HMat2:=TransposedMat(Inverse(HMat));
  Add(ListGen, SYMPL_CreateElement(HMat, ZerMat, ZerMat, HMat2));
  for i in [1..g]
  do
    if i=1 then
      SMat:=NullMat(g, g);
      SMat[1][i]:=eFrac;
    else
      SMat:=NullMat(g, g);
      SMat[1][i]:=eFrac;
      SMat[i][1]:=eFrac;
    fi;
    Add(ListGen, SYMPL_CreateElement(IdMat, ZerMat, SMat, IdMat));
  od;
  return ListGen;
end;


SYMPL_GetGenerators:=function(g)
  local eFrac;
  eFrac:=1;
  return SYMPL_GetGenerators_Fractional(g, eFrac);
end;

SYMPL_RandomElement_Rational:=function(g, MaxVal, eMult)
  local ListGen, RetMat, nb, iter, eFrac;
  RetMat:=IdentityMat(2*g);
  nb:=eMult*g;
  for iter in [1..nb]
  do
    eFrac:=Random([1..MaxVal])/Random([1..MaxVal]);
    ListGen:=SYMPL_GetGenerators_Fractional(g, eFrac);
    RetMat:=RetMat*Random(ListGen);
  od;
  return RetMat;
end;





SYMPL_RandomElement:=function(nb, g)
  local ListGen, RetMat, iter;
  ListGen:=SYMPL_GetGenerators(g);
  RetMat:=IdentityMat(2*g);
  for iter in [1..nb]
  do
    RetMat:=RetMat*Random(ListGen);
  od;
  return RetMat;
end;



SYMPL_GetEvenPermutationGroup:=function(g)
  local ListMatrGen, ListEven, ListPermGens, eGen, eList, phi, GRPmatr, GRPperm;
  ListMatrGen:=SYMPL_GetGenerators(g);
  GRPmatr:=Group(ListMatrGen);
  ListEven:=SYMPL_GetEvenPairs(g);
  ListPermGens:=[];
  for eGen in ListMatrGen
  do
    eList:=List(ListEven, x->Position(ListEven, SYMPL_EvenPairAction(x, eGen)));
    Add(ListPermGens, PermList(eList));
  od;
  GRPperm:=Group(ListPermGens);
  phi:=GroupHomomorphismByImagesNC(GRPmatr, GRPperm, ListMatrGen, ListPermGens);
  return rec(ListPermGens:=ListPermGens, ListMatrGen:=ListMatrGen, GRPperm:=GRPperm, GRPmatr:=GRPmatr, phi:=phi);
end;

SYMPL_GetSymplecticForm:=function(g)
  local eMat, i;
  eMat:=NullMat(2*g, 2*g);
  for i in [1..g]
  do
    eMat[i][g+i]:=1;
    eMat[i+g][i]:=-1;
  od;
  return eMat;
end;


# Given a vector v =[v1, ...., vN]
# Find a matrix M in Sp(N, Z) such that
# vM = [d, 0, ....., 0] with d the gcd of v1, ..., vN
SYMPL_GetVectorReductionMapping:=function(eVect)
  local g, TheMat, a, b, eRec, a11, a12, a21, a22, eVect2, TheGcd, eVect2b, TheCompl, Umat, Utr, rMat, i, j, TheProd, eInvMat;
  g:=Length(eVect)/2;
  TheMat:=NullMat(2*g,2*g);
  for i in [1..g]
  do
    a:=eVect[i];
    b:=eVect[i+g];
    if a=0 and b=0 then
      a11:=1;
      a12:=0;
      a21:=0;
      a22:=1;
    else
      eRec:=GcdVector([a,b]);
      a11:=a/eRec.TheGcd;
      a12:=b/eRec.TheGcd;
      a21:=-eRec.ListCoef[2];
      a22:= eRec.ListCoef[1];
    fi;
    TheMat[i][i]:=a11;
    TheMat[i][i+g]:=a12;
    TheMat[i+g][i]:=a21;
    TheMat[i+g][i+g]:=a22;
  od;
  eVect2:=eVect*Inverse(TheMat);
  if eVect2{[1+g..2*g]}<>ListWithIdenticalEntries(g,0) then
    Error("Matrix error. Please debug");
  fi;
  TheGcd:=GcdVector(eVect2).TheGcd;
  eVect2b:=eVect2{[1..g]}/TheGcd;
  TheCompl:=SubspaceCompletion([eVect2b],g);
  Umat:=Concatenation([eVect2b], TheCompl);
  Utr:=TransposedMat(Inverse(Umat));
  rMat:=NullMat(2*g, 2*g);
  for i in [1..g]
  do
    for j in [1..g]
    do
      rMat[i][j]:=Umat[i][j];
      rMat[i+g][j+g]:=Utr[i][j];
    od;
  od;
  TheProd:=Inverse(TheMat)*Inverse(rMat);
  eInvMat:=SYMPL_GetSymplecticForm(g);
  if TheProd*eInvMat*TransposedMat(TheProd)<>eInvMat then
    Error("The matrix is not symplectic");
  fi;
  return TheProd;
end;


SYMPL_IsLagrangianSubspace:=function(TheBasis)
  local g, eInvMat, TheDim, i, j, eScal;
  g:=Length(TheBasis[1])/2;
  eInvMat:=SYMPL_GetSymplecticForm(g);
  TheDim:=Length(TheBasis);
  for i in [1..TheDim-1]
  do
    for j in [i+1..TheDim]
    do
      eScal:=TheBasis[i]*eInvMat*TheBasis[j];
      if eScal<>0 then
        return false;
      fi;
    od;
  od;
  return true;
end;

# Given a basis [v1, ..., vk] of a Lagrangian subspace in Z^{2n}
# Find a matrix M in Sp(2n,Z) such that
# [v1,....,vN]M= [ [1,0,...,0], [0,1,0,...,0], ...., ]
SYMPL_LagrangianReductionMatrix:=function(TheBasis)
  local TheDim, g, ReturnMat, TheBasisImg, i, TheSubspace, j, eVect, TheCompl, TheUnimod, TheUnimodInv, TheUnimodTr, BigMat1, TheBasisImg2, BigMat2, eSel, RedVect2, RedMat, len, iDim;
  if SYMPL_IsLagrangianSubspace(TheBasis)=false then
    Error("TheBasis does not define a Lagrangian subspace");
  fi;
  TheDim:=Length(TheBasis);
  g:=Length(TheBasis[1])/2;
  ReturnMat:=IdentityMat(2*g);
  TheBasisImg:=TheBasis*ReturnMat;
  for iDim in [1..TheDim]
  do
    #
    #
    eSel:=Concatenation([iDim..g],[iDim+g..2*g]);
    RedVect2:=TheBasisImg[iDim]{eSel};
    RedMat:=SYMPL_GetVectorReductionMapping(RedVect2);
    BigMat2:=IdentityMat(2*g,2*g);
    len:=Length(eSel);
    for i in [1..len]
    do
      for j in [1..len]
      do
        BigMat2[eSel[i]][eSel[j]]:=RedMat[i][j];
      od;
    od;
    TheBasisImg2:=TheBasisImg*BigMat2;
    #
    #
    TheSubspace:=[];
    for j in [1..iDim-1]
    do
      eVect:=ListWithIdenticalEntries(g,0);
      eVect[j]:=1;
      Add(TheSubspace, ShallowCopy(eVect));
    od;
    Add(TheSubspace, TheBasisImg2[iDim]{[1..g]});
    TheCompl:=SubspaceCompletion(TheSubspace,g);
    TheUnimod:=Concatenation(TheSubspace, TheCompl);
    TheUnimodInv:=Inverse(TheUnimod);
    TheUnimodTr:=TransposedMat(TheUnimod);
    BigMat1:=NullMat(2*g,2*g);
    for i in [1..g]
    do
      for j in [1..g]
      do
        BigMat1[i][j]:=TheUnimodInv[i][j];
        BigMat1[i+g][j+g]:=TheUnimodTr[i][j];
      od;
    od;
    TheBasisImg:=TheBasisImg2*BigMat1;
    #
    ReturnMat:=ReturnMat*BigMat2*BigMat1;
  od;
  return ReturnMat;
end;

SYMPL_LagrangianEquivalence:=function(TheBasis1, TheBasis2)
  local RetMat1, RetMat2, TotRetMat;
  RetMat1:=SYMPL_LagrangianReductionMatrix(TheBasis1);
  RetMat2:=SYMPL_LagrangianReductionMatrix(TheBasis2);
  TotRetMat:=RetMat1*Inverse(RetMat2);
  if TheBasis1*TotRetMat<>TheBasis2 then
    Error("bug somewhere");
  fi;
  return TotRetMat;
end;


# We try to follow following paper:
# Hua, L.K., Reiner, I. On the generators of the Symplectic
# modular group
SYMPL_CanonicalLagrangianStabilizer:=function(g, k)
  local ListGen, TheDim, iDim, eSymmVect, eSymmMat, Hmat, i, j, iLine, iCol, Umat, Vmat, eGen, eSet;
  ListGen:=[];
  #
  # First group of stabilizing matrices
  # Matrices of the form 
  # | I 0 |
  # | S I |
  # with S=Str
  #
  TheDim:=g*(g+1)/2;
  for iDim in [1..TheDim]
  do
    eSymmVect:=ListWithIdenticalEntries(TheDim,0);
    eSymmVect[iDim]:=1;
    eSymmMat:=VectorToSymmetricMatrix(eSymmVect, g);
    Hmat:=IdentityMat(2*g,2*g);
    for i in [1..g]
    do
      for j in [1..g]
      do
        Hmat[i+g][j]:=eSymmMat[i][j];
      od;
    od;
    Add(ListGen, Hmat);
  od;
  #
  # Second, matrices of the form
  # | U 0 |
  # | 0 V |
  # with U preserving the space
  for iLine in [k+1..g]
  do
    for iCol in [1..k]
    do
      Umat:=IdentityMat(g, g);
      Umat[iLine][iCol]:=1;
      Vmat:=TransposedMat(Inverse(Umat));
      Hmat:=NullMat(2*g, 2*g);
      for i in [1..g]
      do
        for j in [1..g]
        do
          Hmat[i][j]:=Umat[i][j];
          Hmat[i+g][j+g]:=Vmat[i][j];
        od;
      od;
      Add(ListGen, Hmat);
    od;
  od;
  #
  # Third the matrices of the form
  # | A B |
  # | C D |
  # with each A, B, C, D having a structure of a (k, g-k)
  # matrix
  #
  if k<g then
    eSet:=Concatenation([k+1..g], [g+k+1..2*g]);
    for eGen in SYMPL_GetGenerators(g-k)
    do
      Hmat:=IdentityMat(2*g, 2*g);
      for i in [1..2*(g-k)]
      do
        for j in [1..2*(g-k)]
        do
          Hmat[eSet[i]][eSet[j]]:=eGen[i][j];
        od;
      od;
      Add(ListGen, Hmat);
    od;
  fi;
  return Group(ListGen);
end;


SYMPL_StabilizerLagrangian:=function(eBasis)
  local CanMatrix, g, k, ListGen, eGen, eNewGen;
  CanMatrix:=SYMPL_LagrangianReductionMatrix(eBasis);
  g:=Length(eBasis[1])/2;
  k:=Length(eBasis);
  ListGen:=[];
  for eGen in GeneratorsOfGroup(SYMPL_CanonicalLagrangianStabilizer(g, k))
  do
    eNewGen:=CanMatrix*eGen*Inverse(CanMatrix);
    Add(ListGen, eNewGen);
  od;
  return Group(ListGen);
end;


# See Hua & Reiner
# for the definition of rotation matrix
SYMPL_GetRotation:=function(eMat)
  local n, fMat, RetMat, i, j;
  n:=Length(eMat);
  fMat:=TransposedMat(Inverse(eMat));
  RetMat:=NullMat(2*n, 2*n);
  for i in [1..n]
  do
    for j in [1..n]
    do
      RetMat[i  ][j  ]:=eMat[i][j];
      RetMat[i+n][j+n]:=fMat[i][j];
    od;
  od;
  return RetMat;
end;


SYMPL_GetHeckeOperatorCandidate_A:=function(n,p)
  local eMat, i, eInvMat;
  eMat:=NullMat(2*n,2*n);
  for i in [1..n]
  do
    eMat[i][i]:=p;
    eMat[i+n][i+n]:=1/p;
  od;
  eInvMat:=SYMPL_GetSymplecticForm(n);
  if eMat*eInvMat*TransposedMat(eMat)<>eInvMat then
    Error("Invariance property broken");
  fi;
  return eMat;
end;


SYMPL_GetHeckeOperatorCandidate_B:=function(n,p)
  local eMat, i, eInvMat;
  eMat:=NullMat(2*n,2*n);
  for i in [1..n]
  do
    eMat[i][i]:=p;
    eMat[i+n][i+n]:=1;
  od;
  return eMat;
end;



SYMPL_GetHeckeOperatorCandidate_C:=function(n,p)
  local eMat, i, eInvMat, ListVal;
  if 2*n<>4 then
    Error("We need n=4 for this matrix to be read");
  fi;
  eMat:=NullMat(4,4);
  ListVal:=[p, p*p, p, 1];
  for i in [1..4]
  do
    eMat[i][i]:=ListVal[i];
  od;
  return eMat;
end;


SYMPL_IsMatrixInSpN_Q:=function(eMat)
  local n, eInvMat, eProd;
  n:=Length(eMat)/2;
  eInvMat:=SYMPL_GetSymplecticForm(n);
  eProd:=eMat*eInvMat*TransposedMat(eMat);
  if RemoveFractionMatrix(eProd)<>eInvMat then
    return false;
  fi;
  return true;
end;


#
# We do reduction over the integers of an antisymmetric
# matrix to a canonical one.
SYMPL_CanonicalizeAntisymmetric:=function(eMatAntisym)
  local n, eMatWork, i, j, ReductionMatrix, iColFound, IsFirst, nbDiff, iCol, eVal, MinValue, iColTarget, iRow, eMatTrans, eVal1, eVal2, qVal, eSign, ePerm, res;
  n:=Length(eMatAntisym);
  eMatWork:=NullMat(n,n);
  for i in [1..n]
  do
    for j in [1..n]
    do
      eMatWork[i][j]:=eMatAntisym[i][j];
    od;
  od;
  ReductionMatrix:=IdentityMat(n);
  for i in [1..n]
  do
    while(true)
    do
      iColFound:=-1;
      IsFirst:=1;
      nbDiff:=0;
      for iCol in [1..n]
      do
        eVal:=eMatWork[i][iCol];
        if eVal<>0 then
          if IsFirst=1 then
            MinValue:=AbsInt(eVal);
            iColFound:=iCol;
          else
            if AbsInt(eVal) < MinValue then
              MinValue:=AbsInt(eVal);
              iColFound:=iCol;
            fi;
          fi;
          nbDiff:=nbDiff+1;
          IsFirst:=0;
        fi;
      od;
      if iColFound<>-1 then
        # first put it at right position
        iColTarget:=n+1-i;
        if iColTarget=iColFound then
          ePerm:=();
        else
          ePerm:=(iColTarget,iColFound);
        fi;
        eMatTrans:=NullMat(n,n);
        for iCol in [1..n]
        do
          iRow:=OnPoints(iCol, ePerm);
          eMatTrans[iRow][iCol]:=1;
        od;
        if RankMat(eMatTrans)<n then
          Print("Debug from here 1\n");
          Print(NullMat(5));
        fi;
        ReductionMatrix:=eMatTrans*ReductionMatrix;
        eMatWork:=eMatTrans*eMatWork*TransposedMat(eMatTrans);
        # second put the right sign
        if i<=n/2 then
          eSign:=1;
        else
          eSign:=-1;
        fi;
        if eSign*eMatWork[i][iColTarget]<0 then
          eMatTrans:=IdentityMat(n);
          eMatTrans[iColTarget][iColTarget]:=-1;
          if RankMat(eMatTrans)<n then
            Print("Debug from here 2\n");
            Print(NullMat(5));
          fi;
          ReductionMatrix:=eMatTrans*ReductionMatrix;
          eMatWork:=eMatTrans*eMatWork*TransposedMat(eMatTrans);
        fi;
      fi;
      if nbDiff<=1 then
        break;
      fi;
      for iCol in [1..n]
      do
        if iCol<>iColTarget then
          eVal1:=eMatWork[i][iCol];
          eVal2:=eMatWork[i][iColTarget];
          res:=eVal1 mod eVal2;
          qVal:=(eVal1 - res)/eVal2;
          eMatTrans:=IdentityMat(n,n);
          eMatTrans[iCol][iColTarget]:=-qVal;
          if RankMat(eMatTrans)<n then
            Print("Debug from here 3\n");
            Print(NullMat(5));
          fi;
          ReductionMatrix:=eMatTrans*ReductionMatrix;
          eMatWork:=eMatTrans*eMatWork*TransposedMat(eMatTrans);
        fi;
      od;
    od;
  od;
  return rec(ReductionMatrix:=ReductionMatrix, eMatWork:=eMatWork);
end;





Jnmatrix:=function(n)
  local res, RetMat, i, j, eSign;
  res:=n mod 2;
  if res=1 then
    Print("The dimension should be even\n");
    Print(NullMat(5));
  fi;
  RetMat:=NullMat(n,n);
  for i in [1..n]
  do
    j:=n+1-i;
    if 2*i<=n then
      eSign:=1;
    else
      eSign:=-1;
    fi;
    RetMat[i][j]:=eSign;
  od;
  return RetMat;
end;


#
# We have a configuration of vectors
# and we compute the digraph determing
# the isomorphism
#
SYMPL_GetDigraph:=function(EXT)
  local nbEXT, n, g, Qmat, eEXT, fEXT, Qinv, DiMatrix, SympMat, eLine, eScal1, eScal2, eScal;
  nbEXT:=Length(EXT);
  n:=Length(EXT[1]);
  g:=n/2;
  Qmat:=NullMat(n, n);
  for eEXT in EXT
  do
    Qmat:=Qmat + TransposedMat([eEXT]) * [eEXT];
  od;
  Qinv:=Inverse(Qmat);
  DiMatrix:=[];
  SympMat:=SYMPL_GetSymplecticForm(g);
  for eEXT in EXT
  do
    eLine:=[];
    for fEXT in EXT
    do
      eScal1:=eEXT*Qinv*fEXT;
      eScal2:=eEXT*SympMat*fEXT;
      eScal:=[eScal1, eScal2];
      Add(eLine, eScal);
    od;
    Add(DiMatrix, eLine);
  od;
  return DiMatrix;
end;



SYMPL_GetAutomorphismPerfectDomain:=function(EXT)
  local DiMatrix, GRPperm, ListMatrGens, ListPermGens, ePerm, eMat, GRPmatr;
  DiMatrix:=SYMPL_GetDigraph(EXT);
  GRPperm:=AutomorphismWeightedDigraph(DiMatrix);
  ListMatrGens:=[];
  ListPermGens:=GeneratorsOfGroup(GRPperm);
  for ePerm in ListPermGens
  do
    eMat:=FindTransformation(EXT, EXT, ePerm);
    if IsIntegralMat(eMat)=false then
      Error("Matrix should be integral");
    fi;
    Add(ListMatrGens, eMat);
  od;
  GRPmatr:=Group(ListMatrGens);
  return rec(GRPperm:=GRPperm, GRPmatr:=GRPmatr);
end;

SYMPL_TestEquivalencePerfectDomain:=function(EXT1, EXT2)
  local DiMatrix1, DiMatrix2, test, ePermEquiv, eMatEquiv;
  DiMatrix1:=SYMPL_GetDigraph(EXT1);
  DiMatrix2:=SYMPL_GetDigraph(EXT2);
  test:=IsIsomorphicWeightDigraph(DiMatrix1, DiMatrix2);
  if test=false then
    return fail;
  fi;
  ePermEquiv:=PermList(test);
  eMatEquiv:=FindTransformation(EXT1, EXT2, ePermEquiv);
  if IsIntegralMat(eMatEquiv)=false then
    Error("Matrix should be integral");
  fi;
  return rec(ePermEquiv:=ePermEquiv, eMatEquiv:=eMatEquiv);
end;



TangentSpaceAtIdentity:=function(n)
  local GetPosition, ListEqua, i, j, eEqua, pos1, pos2, ListMatAntiComm, eMatAntiComm, k, eSol, pos, eMat, ListSol, ListMatBasis;
  GetPosition:=function(i,j)
    return i + (j-1)*n;
  end;
  ListEqua:=[];
  for i in [1..n]
  do
    for j in [1..n]
    do
      eEqua:=ListWithIdenticalEntries(n*n, 0);
      pos1:=GetPosition(i, j);
      pos2:=GetPosition(j, i);
      eEqua[pos1]:=eEqua[pos1]+1;
      eEqua[pos2]:=eEqua[pos2]-1;
      Add(ListEqua, eEqua);
    od;
  od;
  ListMatAntiComm:=[Jnmatrix(n)];
  for i in [1..n]
  do
    for j in [1..n]
    do
      for eMatAntiComm in ListMatAntiComm
      do
        eEqua:=ListWithIdenticalEntries(n*n, 0);
        for k in [1..n]
        do
          pos1:=GetPosition(i,k);
          eEqua[pos1]:=eEqua[pos1] + eMatAntiComm[k][j];
          pos2:=GetPosition(k,j);
          eEqua[pos2]:=eEqua[pos2] + eMatAntiComm[i][k];
          Add(ListEqua, eEqua);
        od;
      od;
    od;
  od;
  ListSol:=NullspaceMat(TransposedMat(ListEqua));
  ListMatBasis:=[];
  for eSol in ListSol
  do
    eMat:=NullMat(n,n);
    for i in [1..n]
    do
      for j in [1..n]
      do
        pos:=GetPosition(i,j);
        eMat[i][j]:=eSol[pos];
      od;
    od;
    if eMat<>TransposedMat(eMat) then
      Print("Matrix error 1\n");
      Print(NullMat(5));
    fi;
    for eMatAntiComm in ListMatAntiComm
    do
      if eMat*eMatAntiComm<>-eMatAntiComm*eMat then
        Print("Matrix error 2\n");
        Print(NullMat(5));
      fi;
    od;
    Add(ListMatBasis, eMat);
  od;
  return ListMatBasis;
end;



PARAMODULAR_ExtendLagrangian:=function(TheLagr, eMatAntisym)
  local n, k, TheCompl, TotalBasis, eProduct, Bmat, NSP, eVect, TheRet;
  n:=Length(eMatAntisym);
  k:=Length(TheLagr);
  TheCompl:=SubspaceCompletion(TheLagr, n);
  TotalBasis:=Concatenation(TheLagr, TheCompl);
  eProduct:=TotalBasis*eMatAntisym*TransposedMat(TotalBasis);
  Bmat:=List(eProduct{[1..k]}, x->eProduct{[k+1..n]});
  NSP:=NullspaceMat(TransposedMat(Bmat));
  if Length(NSP)=0 then
    Error("Should be nontrivial");
  fi;
  eVect:=Concatenation(ListWithIdenticalEntries(k,0), NSP[1]);
  TheRet:=Concatenation(TheLagr, eVect*TotalBasis);
  return TheRet;
end;



SYMPL_ComputeSymplecticBasis:=function(ListVect)
  local n, SympFormMat, GetInitialVector, GetPairVector, CompleteBasis, i, WorkingFamily, w1, wN, NewFamily, scal1, scalN, eVect, NewVect;
  n:=Length(ListVect[1])/2;
  SympFormMat:=SYMPL_GetSymplecticForm(n);
  GetInitialVector:=function(LVect)
    local eVect, eSum;
    for eVect in LVect
    do
      eSum:=Sum(List(eVect, AbsInt));
      if eSum>0 then
        return eVect / AbsInt(Gcd(eVect));
      fi;
    od;
    Error("Could not find a non-zero vector");
  end;
  GetPairVector:=function(w1, LVect)
    local ListScal, eGCD, SumVect, iVect;
    ListScal:=List(LVect, x->w1 * SympFormMat * x);
    eGCD:=GcdVector(ListScal);
    if eGCD.TheGcd<>1 then
      Error("The family is not generating eGCD=", eGCD);
    fi;
    SumVect:=ListWithIdenticalEntries(2*n, 0);
    for iVect in [1..Length(LVect)]
    do
      SumVect:=SumVect + eGCD.ListCoef[iVect] * LVect[iVect];
    od;
    return SumVect;
  end;
  CompleteBasis:=[];
  for i in [1..n]
  do
    CompleteBasis[i]:="unset";
  od;
  WorkingFamily:=StructuralCopy(ListVect);
  for i in [1..n]
  do
    w1:=GetInitialVector(WorkingFamily);
    wN:=GetPairVector(w1, WorkingFamily);
    CompleteBasis[i]:=w1;
    CompleteBasis[n+i]:=wN;
    NewFamily:=[];
    for eVect in WorkingFamily
    do
      scal1:=eVect * SympFormMat * w1;
      scalN:=eVect * SympFormMat * wN;
      NewVect:=eVect - scalN * w1 + scal1 * wN;
      Add(NewFamily, NewVect);
    od;
    WorkingFamily:=NewFamily;
  od;
  return CompleteBasis;
end;
