#
# TheDelaunay contains 3 records
#   n
#   EXT, list of vertices
#   VectSpace, direction of change
#   TheQuadForm
#   TheQuadFunction

#
# the space spanned by eBasis1 is supposed to a subspace of
# the space spanned by eBasis2
InfDel_BasisCompletion:=function(eBasis1, eBasis2, n)
  local eBasis1ins, TheCompl;
  eBasis1ins:=List(eBasis1, x->SolutionMat(eBasis2, x));
  TheCompl:=SubspaceCompletion(eBasis1ins, Length(eBasis2));
  if Length(TheCompl)=0 then
    return [];
  fi;
  return TheCompl*eBasis2;
end;

InfDel_GetAffineBasis:=function(TheBasis)
  local AffBasis, eVect, n;
  n:=Length(TheBasis[1]);
  AffBasis:=[];
  eVect:=ListWithIdenticalEntries(n+1,0);
  eVect[1]:=1;
  Add(AffBasis, eVect);
  Append(AffBasis, List(TheBasis, x->Concatenation([0], x)));
  return AffBasis;
end;

InfDel_GetQuadForm:=function(TheQuadFunction)
  local n;
  n:=Length(TheQuadFunction)-1;
  return List(TheQuadFunction{[2..n+1]}, x->x{[2..n+1]});
end;



InfDel_ZerForm:=function(n)
  return rec(n:=n,
             EXT:=[Concatenation([1], ListWithIdenticalEntries(n, 0))], 
             VectSpace:=IdentityMat(n),
             TheQuadFunction:=NullMat(n+1,n+1),
             TheQuadForm:=NullMat(n,n));
end;



InfDel_GetIntegerBasis:=function(n, TheBasis)
  local NSP;
  if RankMat(TheBasis)=n then
    return IdentityMat(n);
  fi;
  NSP:=NullspaceIntMat(TransposedMat(TheBasis));
  return NullspaceIntMat(TransposedMat(NSP));
end;


InfDel_GetLinSpaceFromPolytope:=function(EXT)
  local n, LinSpace;
  n:=Length(EXT[1])-1;
  LinSpace:=List(EXT, x->x{[2..n+1]}-EXT[1]{[2..n+1]});
  return InfDel_GetIntegerBasis(n, LinSpace);
end;


InfDel_Get012form:=function(TheDelaunay, TheQuadForm)
  local n, LinEXT, p, TheBasis, AffBasis, NewQuadForm, NewQuadFormRed, NewEXT, NewEXTred, CP, eCenterNew, eCenter, eProd, eScal, TheQuadFunction, i, j, iVert;
  n:=TheDelaunay.n;
  LinEXT:=InfDel_GetLinSpaceFromPolytope(TheDelaunay.EXT);
  if Length(TheDelaunay.VectSpace)> 0 then
    for iVert in [2..Length(TheDelaunay.EXT)]
    do
      if SolutionMat(TheDelaunay.VectSpace, TheDelaunay.EXT[iVert]{[2..n+1]}-TheDelaunay.EXT[1]{[2..n+1]})<>fail then
        Print("Some vector of VectSpace also are obtained as difference\n");
        Print("of vertices. This cannot be allowed\n");
        Error("Please correct");
      fi;
    od;
  fi;
  p:=Length(LinEXT);
  TheBasis:=Concatenation(LinEXT, TheDelaunay.VectSpace);
  AffBasis:=InfDel_GetAffineBasis(TheBasis);
  NewQuadForm:=TheBasis*TheQuadForm*TransposedMat(TheBasis);
  NewQuadFormRed:=List(NewQuadForm{[1..p]}, x->x{[1..p]});
  NewEXT:=TheDelaunay.EXT*Inverse(AffBasis);
  NewEXTred:=List(NewEXT, x->x{[1..p+1]});
  CP:=CenterRadiusDelaunayPolytopeGeneral(NewQuadFormRed, NewEXTred);
  eCenterNew:=Concatenation(CP.Center, ListWithIdenticalEntries(n-p,0));
  eCenter:=eCenterNew*AffBasis;
  eProd:=-eCenter{[2..n+1]}*TheQuadForm;
  eScal:=-eProd*eCenter{[2..n+1]};
  TheQuadFunction:=NullMat(n+1,n+1);
  for i in [1..n]
  do
    for j in [1..n]
    do
      TheQuadFunction[i+1][j+1]:=TheQuadForm[i][j];
    od;
    TheQuadFunction[1][i+1]:=eProd[i];
    TheQuadFunction[i+1][1]:=eProd[i];
  od;
  TheQuadFunction[1][1]:=eScal-CP.SquareRadius;
  return TheQuadFunction;
end;

InfDel_GetCharMatrix:=function(EXT)
  local p, Zmat, eEXT;
  p:=Length(EXT[1]);
  Zmat:=NullMat(p,p);
  for eEXT in EXT
  do
    Zmat:=Zmat+TransposedMat([eEXT])*[eEXT];
  od;
  return Inverse(Zmat);
end;

InfDel_SolutionMatMod1:=function(ListIntVect, eRatVect)
  local eRMact, n, TheBasis, eSol, eSolRed, DimIntSpace;
  eRMact:=RemoveFractionPlusCoef(eRatVect);
  DimIntSpace:=Length(ListIntVect);
  n:=Length(eRatVect);
  TheBasis:=Concatenation(ListIntVect, eRMact.TheMult*IdentityMat(n));
  eSol:=SolutionIntMat(TheBasis, eRMact.TheVect);
  if eSol=fail then
    return fail;
  else
    eSolRed:=eRatVect - eSol{[1..DimIntSpace]}*ListIntVect;
    if IsIntegralVector(eSolRed)=false then
      Error("Please debug from here SolutionMatMod1");
    fi;
    return eSolRed;
  fi;
end;

InfDel_Intersection:=function(TheDelaunay1, TheDelaunay2)
  local n, ListEqua1, ListEqua2, ListEqua, VectSpaceInt, SPCdiff1, SPCdiff2, AffSPCdiff1, AffSPCdiff2, nb1, nb2, TheConcat, NewEXT, eEXT1, eEXT2, ListB, eSol, eSol1, eSol2, fEXTcand1, fEXTcand2, AffVectSpaceInt, eSolCheck, eSolMod1;
  n:=TheDelaunay1.n;
  if Length(TheDelaunay1.VectSpace)=0 then
    ListEqua1:=IdentityMat(n);
  else
    ListEqua1:=NullspaceIntMat(TransposedMat(TheDelaunay1.VectSpace));
  fi;
  if Length(TheDelaunay2.VectSpace)=0 then
    ListEqua2:=IdentityMat(n);
  else
    ListEqua2:=NullspaceIntMat(TransposedMat(TheDelaunay2.VectSpace));
  fi;
  ListEqua:=Concatenation(ListEqua1, ListEqua2);
  VectSpaceInt:=NullspaceIntMat(TransposedMat(ListEqua));
  #
#  Print("|VectSpaceInt|=", Length(VectSpaceInt), "\n");
#  Print("|TheDelaunay1.VectSpace|=", Length(TheDelaunay1.VectSpace), "\n");
#  Print("|TheDelaunay2.VectSpace|=", Length(TheDelaunay2.VectSpace), "\n");
  SPCdiff1:=InfDel_BasisCompletion(VectSpaceInt, TheDelaunay1.VectSpace, n);
  SPCdiff2:=InfDel_BasisCompletion(VectSpaceInt, TheDelaunay2.VectSpace, n);
  AffSPCdiff1:=List(SPCdiff1, x->Concatenation([0], x));
  AffSPCdiff2:=List(SPCdiff2, x->Concatenation([0], x));
  AffVectSpaceInt:=List(VectSpaceInt, x->Concatenation([0], x));
  nb1:=Length(AffSPCdiff1);
  nb2:=Length(AffSPCdiff2);
  #
  TheConcat:=Concatenation(AffSPCdiff1, -AffSPCdiff2, AffVectSpaceInt);
  if Length(TheConcat)>0 then
    NewEXT:=[];
    for eEXT1 in TheDelaunay1.EXT
    do
      for eEXT2 in TheDelaunay2.EXT
      do
        ListB:=eEXT1-eEXT2;
        eSol:=SolutionMat(TheConcat, ListB);
        if eSol<>fail then
          eSol1:=eSol{[1..nb1]};
          eSol2:=eSol{[nb1+1..nb1+nb2]};
          if Length(eSol1)>0 then
            fEXTcand1:=eEXT1-eSol1*AffSPCdiff1;
          else
            fEXTcand1:=eEXT1;
          fi;
          if Length(eSol2)>0 then
            fEXTcand2:=eEXT2-eSol2*AffSPCdiff2;
          else
            fEXTcand2:=eEXT2;
          fi;
          if Length(AffVectSpaceInt)=0 then
            if fEXTcand1<>fEXTcand2 then
              Error("Inconsistency in the program 1");
            fi;
            if IsIntegralVector(fEXTcand1)=true then
              Add(NewEXT, fEXTcand1);
            fi;
          else
            eSolCheck:=SolutionMat(AffVectSpaceInt, fEXTcand1-fEXTcand2);
            if eSolCheck=fail then
              Error("Inconsistency in the program 2");
            fi;
            eSolMod1:=InfDel_SolutionMatMod1(AffVectSpaceInt, fEXTcand1);
            if eSolMod1<>fail then
              Add(NewEXT, eSolMod1);
            fi;
          fi;
        fi;
      od;
    od;
    if Length(Set(NewEXT))<>Length(NewEXT) then
      Error("Inconsistency in the program 3");
    fi;
  else
    NewEXT:=Intersection(Set(TheDelaunay1.EXT), Set(TheDelaunay2.EXT));
  fi;
  return rec(n:=n, EXT:=NewEXT, VectSpace:=VectSpaceInt);
end;



InfDel_Canonicalize:=function(eDelaunay)
  local n, TheCompl, NewBasis, AffBasis, p, NewEXT, eEXT, hEXT, eNewEXT;
  n:=eDelaunay.n;
  TheCompl:=InfDel_BasisCompletion(eDelaunay.VectSpace, IdentityMat(n), n);
  NewBasis:=Concatenation(TheCompl, eDelaunay.VectSpace);
  AffBasis:=InfDel_GetAffineBasis(NewBasis);
  p:=Length(TheCompl);
  NewEXT:=[];
  for eEXT in eDelaunay.EXT
  do
    hEXT:=eEXT*Inverse(AffBasis);
    hEXT{[p+2..n]}:=ListWithIdenticalEntries(n-(p+1),0);
    eNewEXT:=hEXT*AffBasis;
    Add(NewEXT, eNewEXT);
  od;
  return rec(n:=n, EXT:=Set(NewEXT), VectSpace:=eDelaunay.VectSpace, TheQuadForm:=eDelaunay.TheQuadForm, TheQuadFunction:=eDelaunay.TheQuadFunction);
end;



# here the Delaunay is assumed to be canonicalized
InfDel_IsFullDimensional:=function(eDelaunay)
  local rnk, n;
  n:=eDelaunay.n;
  rnk:=RankMat(eDelaunay.EXT);
  if rnk+Length(eDelaunay.VectSpace)<>n+1 then
    return false;
  fi;
  return true;
end;


InfDel_MergeDistMatrices:=function(ListDistMat)
  local nbPt, nbMat, eList, i, j, TheDistMat;
  nbPt:=Length(ListDistMat[1]);
  nbMat:=Length(ListDistMat);
  TheDistMat:=NullMat(nbPt, nbPt);
  for i in [1..nbPt]
  do
    for j in [1..nbPt]
    do
      eList:=List(ListDistMat, x->x[i][j]);
      TheDistMat[i][j]:=eList;
    od;
  od;
  return TheDistMat;
end;



InfDel_GetGramDiscMat:=function(TheDelaunay, TheEXT)
  local n, TheSPC, p, TheBasis, AffBasis, NewEXT, NewEXTred, Zmat, nbVert, GramMat_Discriminant, iVert, jVert, TheScal, eNewEXTred_i, eNewEXTred_j, eNewEXT_i, eNewEXT_j, InvAff;
  n:=TheDelaunay.n;
  TheSPC:=InfDel_BasisCompletion(TheDelaunay.VectSpace, IdentityMat(n), n);
  p:=Length(TheSPC);
  TheBasis:=Concatenation(TheSPC, TheDelaunay.VectSpace);
  AffBasis:=InfDel_GetAffineBasis(TheBasis);
  InvAff:=Inverse(AffBasis);
  NewEXT:=TheDelaunay.EXT*InvAff;
  NewEXTred:=List(NewEXT, x->x{[1..p+1]});
  Zmat:=InfDel_GetCharMatrix(NewEXTred);
  nbVert:=Length(TheEXT);
  GramMat_Discriminant:=NullMat(nbVert, nbVert);
  for iVert in [1..nbVert]
  do
    for jVert in [iVert..nbVert]
    do
      eNewEXT_i:=TheEXT[iVert]*InvAff;
      eNewEXT_j:=TheEXT[jVert]*InvAff;
      eNewEXTred_i:=eNewEXT_i{[1..p+1]};
      eNewEXTred_j:=eNewEXT_j{[1..p+1]};
      TheScal:=eNewEXTred_i*Zmat*eNewEXTred_j;
      GramMat_Discriminant[iVert][jVert]:=TheScal;
      GramMat_Discriminant[jVert][iVert]:=TheScal;
    od;
  od;
  return GramMat_Discriminant;
end;

InfDel_AffineTransformation:=function(TheDelaunay, AffBasis)
  local TheBasis, TheRec, TheVectSpace;
  TheBasis:=FuncExplodeBigMatrix(AffBasis).MatrixTransformation;
  if Length(TheDelaunay.VectSpace)=0 then
    TheVectSpace:=[];
  else
    TheVectSpace:=TheDelaunay.VectSpace*Inverse(TheBasis);
  fi;
  TheRec:=rec(n:=TheDelaunay.n, EXT:=TheDelaunay.EXT*Inverse(AffBasis), VectSpace:=TheVectSpace);
  if IsBound(TheDelaunay.TheQuadForm)=true then
    TheRec.TheQuadForm:=TheBasis*TheDelaunay.TheQuadForm*TransposedMat(TheBasis);
  fi;
  if IsBound(TheDelaunay.TheQuadFunction)=true then
    TheRec.TheQuadFunction:=AffBasis*TheDelaunay.TheQuadFunction*TransposedMat(AffBasis);
  fi;
  if IsBound(TheDelaunay.ListAdjacentVert)=true then
    TheRec.ListAdjacentVert:=TheDelaunay.ListAdjacentVert*Inverse(AffBasis);
  fi;
  return TheRec;
end;









InfDel_GetZeroSetKernel:=function(eQuadFunction)
  local n, eQuadForm, VectSpace, TheSPC, p, TheBasis, AffBasis, NewQuadFunction, NewQuadFuncRed, NewQuadForm, hVect, RedQuadForm, hVectRed, cCentRed, rSquareRed, TheCVP, TheCVPext, TheVectSpace, TheRec, NewVectSpace, eVect, negVect, negVal, j, eSign, eVal, rVect, ListNeg, eMult, eIntVect, eVert;
  n:=Length(eQuadFunction)-1;
  eQuadForm:=InfDel_GetQuadForm(eQuadFunction);
  if IsPositiveSymmetricMatrix(eQuadForm)=false then
    ListNeg:=GetSetNegativeVector(eQuadForm);
    eMult:=1;
    while(true)
    do
      for eVect in ListNeg
      do
        eIntVect:=List(eMult*eVect, NearestInteger);
        eVert:=Concatenation([1], eIntVect);
        if eVert*eQuadFunction*eVert<0 then
          return rec(error:="TheQuadForm is not positive semidefinite", eVect:=eVect);
        fi;
      od;
      eMult:=eMult+1;
    od;
  fi;
  VectSpace:=NullspaceIntMat(RemoveFractionMatrix(eQuadForm));
  TheSPC:=InfDel_BasisCompletion(VectSpace, IdentityMat(n), n);
  p:=Length(TheSPC);
  TheBasis:=Concatenation(TheSPC, VectSpace);
  AffBasis:=InfDel_GetAffineBasis(TheBasis);
  NewQuadFunction:=AffBasis*eQuadFunction*TransposedMat(AffBasis);
  NewQuadFuncRed:=List(NewQuadFunction{[1..p+1]}, x->x{[1..p+1]});
  hVect:=NewQuadFunction[1]{[2..n+1]};
  if hVect{[p+1..n]}<>ListWithIdenticalEntries(n-p,0) then
    for j in [p+1..n]
    do
      if hVect[j]<>0 then
        eSign:=SignFunction(hVect[j]);
        rVect:=Concatenation([1],ListWithIdenticalEntries(n,0));
        while(true)
        do
          eVal:=rVect*NewQuadFunction*rVect;
          if eVal<0 then
            negVect:=rVect*AffBasis;
            negVal:=negVect*eQuadFunction*negVect;
            if negVal<>eVal then
              Error("Inconsistency here. DEBUG");
            fi;
            return rec(error:="zero vector inconsistency", eVect:=negVect);
          fi;
          rVect[1+j]:=rVect[1+j] - eSign;
        od;
      fi;
    od;
  fi;
  if p=0 then
    if NewQuadFunction[1][1]<0 then
      return rec(error:="the function is constantly negative",
                 eVect:=Concatenation([1], ListWithIdenticalEntries(n,0)));
    fi;
    if NewQuadFunction[1][1]>0 then
      TheRec:=rec(n:=n, EXT:=[], VectSpace:=[]);
      return rec(TheRec:=TheRec);
    fi;
    if NewQuadFunction[1][1]=0 then
      return rec(TheRec:=InfDel_ZerForm(n));
    fi;
  fi;
  RedQuadForm:=List(NewQuadFuncRed{[2..p+1]}, x->x{[2..p+1]});
  hVectRed:=hVect{[1..p]};
  cCentRed:=-hVectRed*Inverse(RedQuadForm);
  rSquareRed:=cCentRed*RedQuadForm*cCentRed-NewQuadFuncRed[1][1];
  TheCVP:=CVPVallentinProgram(RedQuadForm, cCentRed);
  if TheCVP.TheNorm<rSquareRed then
    eVect:=Concatenation([1], TheCVP.ListVect[1], ListWithIdenticalEntries(n-p,0))*AffBasis;
    if eVect*eQuadFunction*eVect >= 0 then
      Error("The value should be strictly negative");
    fi;
    return rec(error:="There are points with negative value at integral points", eVect:=eVect);
  fi;
  if TheCVP.TheNorm>rSquareRed then
    TheRec:=rec(n:=n, EXT:=[], VectSpace:=[]);
    return rec(TheRec:=TheRec);
  fi;
  TheCVPext:=List(TheCVP.ListVect, x->Concatenation([1], x, ListWithIdenticalEntries(n-p,0)));
  TheVectSpace:=IdentityMat(n){[p+1..n]};
  if Length(TheVectSpace)=0 then
    NewVectSpace:=[];
  else
    NewVectSpace:=TheVectSpace*TheBasis;
  fi;
  TheRec:=rec(n:=n, EXT:=TheCVPext*AffBasis, VectSpace:=NewVectSpace);
  return rec(TheRec:=TheRec);
end;


InfDel_GetZeroSet:=function(eQuadFunction)
  return InfDel_GetZeroSetKernel(eQuadFunction).TheRec;
end;

InfDel_GetRealMinimalPoint:=function(TheFunc)
  local n, QuadForm, eVect, xCent, fVect, eVal, xCentInt, fVectInt, eValInt;
  n:=Length(TheFunc)-1;
  QuadForm:=List(TheFunc{[2..n+1]}, x->x{[2..n+1]});
  if RankMat(QuadForm)<n then
    return rec(success:=false);
  fi;
  eVect:=TheFunc[1]{[2..n+1]};
  xCent:=-eVect*Inverse(QuadForm);
  fVect:=Concatenation([1], xCent);
  eVal:=fVect*TheFunc*fVect;
  xCentInt:=List(xCent, NearestInteger);
  fVectInt:=Concatenation([1], xCentInt);
  eValInt:=fVectInt*TheFunc*fVectInt;
  return rec(success:=true, xCent:=xCent, eVal:=eVal, xCentInt:=xCentInt, eValInt:=eValInt);
end;



InfDel_IsFunctionNonNegative:=function(eQuadFunction)
  local TheReply;
  TheReply:=InfDel_GetZeroSetKernel(eQuadFunction);
  if IsBound(TheReply.TheRec)=true then
    return true;
  fi;
  return false;
end;

# check if TheDelaunay1 is a subset of TheDelaunay2
InfDel_IsSubset:=function(TheDelaunay1, TheDelaunay2)
  local n, eVect, H, eEXT, Hspann, eEXTdiff, iCol, AffVectSpace1, AffVectSpace2, nb2, nbVert2;
  n:=TheDelaunay1.n;
  AffVectSpace1:=List(TheDelaunay1.VectSpace, x->Concatenation([0],x));
  AffVectSpace2:=List(TheDelaunay2.VectSpace, x->Concatenation([0],x));
  nb2:=Length(AffVectSpace2);
  if nb2=0 and Length(AffVectSpace1)>0 then
    return false;
  fi;
  for eVect in AffVectSpace1
  do
    if SolutionMat(AffVectSpace2, eVect)=fail then
      return false;
    fi;
  od;
  nbVert2:=Length(TheDelaunay2.EXT);
  for eEXT in TheDelaunay1.EXT
  do
    if Length(AffVectSpace2)=0 then
      if Position(TheDelaunay2.EXT, eEXT)=fail then
        return false;
      fi;
    else
      Hspann:=Concatenation(TheDelaunay2.EXT, AffVectSpace2);
      H:=SolutionIntMat(Hspann, eEXT);
      if H=fail then
        return false;
      fi;
      eEXTdiff:=eEXT - H{[nbVert2+1..nbVert2+nb2]}*AffVectSpace2;
      if Position(TheDelaunay2.EXT, eEXTdiff)=fail then
        return false;
      fi;
    fi;
  od;
  return true;
end;


InfDel_IsEqual:=function(TheDelaunay1, TheDelaunay2)
  if InfDel_IsSubset(TheDelaunay1, TheDelaunay2)=false then
    return false;
  fi;
  if InfDel_IsSubset(TheDelaunay2, TheDelaunay1)=false then
    return false;
  fi;
  return true;
end;

InfDel_IsEquivalence:=function(TheDelaunay1, TheDelaunay2, eEquivMat)
  local TheImage;
  if IsIntegralMat(eEquivMat)=false then
    return false;
  fi;
  if AbsInt(DeterminantMat(eEquivMat))<>1 then
    return false;
  fi;
  TheImage:=InfDel_AffineTransformation(TheDelaunay1, Inverse(eEquivMat));
  return InfDel_IsEqual(TheImage, TheDelaunay2);
end;

InfDel_IsStabilizer:=function(TheDelaunay, TheMatrGroup)
  local eBigGen;
  for eBigGen in GeneratorsOfGroup(TheMatrGroup)
  do
    if InfDel_IsEquivalence(TheDelaunay, TheDelaunay, eBigGen)=false then
      return false;
    fi;
  od;
  return true;
end;


InfDel_GetEquivalence:=function(TheDelaunay1, TheDelaunay2, eGen)
  local n, TheSPC1, p1, TheBasis1, AffBasis1, NewEXT1, NewEXTred1, TheSPC2, p2, TheBasis2, AffBasis2, NewEXT2, NewEXTred2, eMatrGen, eBigMatrGen, i, j, eEquivMatr;
  n:=TheDelaunay1.n;
  TheSPC1:=InfDel_BasisCompletion(TheDelaunay1.VectSpace, IdentityMat(n), n);
  p1:=Length(TheSPC1);
  TheBasis1:=Concatenation(TheSPC1, TheDelaunay1.VectSpace);
  AffBasis1:=InfDel_GetAffineBasis(TheBasis1);
  NewEXT1:=TheDelaunay1.EXT*Inverse(AffBasis1);
  NewEXTred1:=List(NewEXT1, x->x{[1..p1+1]});
  #
  TheSPC2:=InfDel_BasisCompletion(TheDelaunay2.VectSpace, IdentityMat(n), n);
  p2:=Length(TheSPC2);
  TheBasis2:=Concatenation(TheSPC2, TheDelaunay2.VectSpace);
  AffBasis2:=InfDel_GetAffineBasis(TheBasis2);
  NewEXT2:=TheDelaunay2.EXT*Inverse(AffBasis2);
  NewEXTred2:=List(NewEXT2, x->x{[1..p2+1]});
  if p1<>p2 then
    Error("There is a dimension problem");
  fi;
  eMatrGen:=FindTransformation(NewEXTred1, NewEXTred2, eGen);
  if eMatrGen=fail then
    Error("No equivalence found, please debug from here");
  fi;
  if IsIntegralMat(eMatrGen)=false or AbsInt(DeterminantMat(eMatrGen))<>1 then
    Error("We failed the math, we have to go back to the drawing board");
  fi;
  eBigMatrGen:=IdentityMat(n+1);
  for i in [1..p1+1]
  do
    for j in [1..p1+1]
    do
      eBigMatrGen[i][j]:=eMatrGen[i][j];
    od;
  od;
  eEquivMatr:=Inverse(AffBasis1)*eBigMatrGen*AffBasis2;
  if InfDel_IsEquivalence(TheDelaunay1, TheDelaunay2, eEquivMatr)=false then
    Error("We are doing something wrong in the matrices");
  fi;
  return eEquivMatr;
end;



InfDel_CheckCoherencyDelaunay:=function(TheDelaunay)
  local eEXT, eVect, n, NSP, VectSpaceInt, TheM;
  n:=TheDelaunay.n;
  for eEXT in TheDelaunay.EXT
  do
    if eEXT*TheDelaunay.TheQuadFunction*eEXT<>0 then
      Error("The quadratic function does not zero the vertices");
    fi;
  od;
  if IsPositiveSymmetricMatrix(TheDelaunay.TheQuadForm)=false then
    Error("TheQuadForm is not positive semidefinite");
  fi;
  if TransposedMat(TheDelaunay.TheQuadFunction)<>TheDelaunay.TheQuadFunction then
    Error("TheQuadFunction is not symmetric");
  fi;
  for eVect in TheDelaunay.VectSpace
  do
    if eVect*TheDelaunay.TheQuadForm*eVect<>0 then
      Error("Some of the VectSpace vectors are not zero by the quad form");
    fi;
  od;
  for eEXT in TheDelaunay.EXT
  do
    if Length(eEXT)<>TheDelaunay.n+1 then
      Error("The length are not coherent");
    fi;
  od;
  if Length(TheDelaunay.TheQuadForm)<>TheDelaunay.n then
    Error("Lengths are not coherent");
  fi;
  if InfDel_GetQuadForm(TheDelaunay.TheQuadFunction)<>TheDelaunay.TheQuadForm then
    Error("TheQuadForm and TheQuadFunction are not coherent");
  fi;
  if Length(TheDelaunay.VectSpace)>0 then
    NSP:=NullspaceIntMat(TransposedMat(TheDelaunay.VectSpace));
    if Length(NSP)=0 then
      VectSpaceInt:=IdentityMat(n);
    else
      VectSpaceInt:=NullspaceIntMat(TransposedMat(NSP));
    fi;
    TheM:=List(VectSpaceInt, x->SolutionMat(TheDelaunay.VectSpace, x));
    if IsIntegralMat(TheM)=false or AbsInt(DeterminantMat(TheM))<>1 then
      Error("The VectSpace is not correct");
    fi;
  fi;
  if InfDel_IsEqual(TheDelaunay, InfDel_GetZeroSet(TheDelaunay.TheQuadFunction))=false then
    Error("We do not have equality of zero set with advertised quadratic function");
  fi;
end;




InfDel_CheckTechnicalInclusion:=function(TheSuperPolytope, ThePolytope)
  local TheSPCsuper, TheSPC, TheCompl;
  TheSPCsuper:=InfDel_GetLinSpaceFromPolytope(TheSuperPolytope.EXT);
  TheSPC:=InfDel_GetLinSpaceFromPolytope(ThePolytope.EXT);
  TheCompl:=InfDel_BasisCompletion(TheSPCsuper, TheSPC, ThePolytope.n);
end;


#
# We rewrite the coordinates of the polytopes so that the
# subspace spanned by the vertices of TheSuperPolytope
# is contained in the subspace spanned by the vertices of
# the polytope.
# this is a technical manipulation that does not change
# the nature of the object
#
# the VectSpace of the superpolytope contains the
# VectSpace of ThePolytope.
# thus we can do operation with vectors in the vectspace of
# ThePolytope
InfDel_RewriteCoordinate:=function(TheSuperPolytope, ThePolytope)
  local n, TheSPCsuper, TheBasisSuper, AffBasisSuper, TheSPC, p, TheBasis, AffBasis, nb, NewEXT, TheNewSuperPolytope, eNewEXT, RewriteVertex, TheNewListAdjacentVert;
  n:=ThePolytope.n;
  TheSPCsuper:=InfDel_GetLinSpaceFromPolytope(TheSuperPolytope.EXT);
  TheBasisSuper:=Concatenation(TheSPCsuper, TheSuperPolytope.VectSpace);
  AffBasisSuper:=InfDel_GetAffineBasis(TheBasisSuper);
  #
  TheSPC:=InfDel_GetLinSpaceFromPolytope(ThePolytope.EXT);
  p:=Length(TheSPC);
  TheBasis:=Concatenation(TheSPC, ThePolytope.VectSpace);
  AffBasis:=InfDel_GetAffineBasis(TheBasis);
  nb:=Length(TheBasis);
  NewEXT:=[];
  RewriteVertex:=function(eEXT)
    local eSol, eSolB;
    eSol:=SolutionMat(AffBasis, eEXT);
    eSolB:=Concatenation(eSol{[1..p+1]}, ListWithIdenticalEntries(n-p, 0));
    return eSolB*AffBasis;
  end;
  NewEXT:=List(TheSuperPolytope.EXT, RewriteVertex);
  TheNewSuperPolytope:=rec(n:=n, EXT:=NewEXT, VectSpace:=TheSuperPolytope.VectSpace);
  if IsBound(TheSuperPolytope.TheQuadFunction)=true then
    TheNewSuperPolytope.TheQuadFunction:=TheSuperPolytope.TheQuadFunction;
  fi;
  if IsBound(TheSuperPolytope.TheQuadForm)=true then
    TheNewSuperPolytope.TheQuadForm:=TheSuperPolytope.TheQuadForm;
  fi;
  if IsBound(TheSuperPolytope.Status)=true then
    TheNewSuperPolytope.Status:=TheSuperPolytope.Status;
  fi;
  if IsBound(TheSuperPolytope.ListAdjacentVert)=true then
    TheNewListAdjacentVert:=List(TheSuperPolytope.ListAdjacentVert, RewriteVertex);
    TheNewSuperPolytope.ListAdjacentVert:=TheNewListAdjacentVert;
  fi;
  if InfDel_IsEqual(TheNewSuperPolytope, TheSuperPolytope)=false then
    Error("We have done something wrong somewhere");
  fi;
  InfDel_CheckTechnicalInclusion(TheNewSuperPolytope, ThePolytope);
  return TheNewSuperPolytope;
end;


# the inner stabilizer actually.
# The group generated by translations, and GLr(Z)
# is called the affine group and is a finite group.
InfDel_Stabilizer:=function(TheDelaunay)
  local n, SPCinner, TheBasis, p, AffBasis, nbVert, GramMat_Discriminant, TheScal, GRPperm, NewListMatrGens, GRPmatr, LDim, BigEXT, ListPermGens, phi, ListMatrGens;
  GramMat_Discriminant:=InfDel_GetGramDiscMat(TheDelaunay, TheDelaunay.EXT);
  GRPperm:=AutomorphismGroupColoredGraph(GramMat_Discriminant);
  ListPermGens:=GeneratorsOfGroup(GRPperm);
  ListMatrGens:=List(ListPermGens, x->InfDel_GetEquivalence(TheDelaunay, TheDelaunay, x));
  GRPmatr:=Group(ListMatrGens);
  phi:=GroupHomomorphismByImagesNC(GRPperm, GRPmatr, ListPermGens, ListMatrGens);
  return rec(GRPperm:=GRPperm, GRPmatr:=GRPmatr, phi:=phi);
end;




# Sometimes, just the inner stabilizer is enough, but
# sometimes we really need all generators of the group
InfDel_CompleteStabilizer:=function(TheDelaunay)
  local n, SPCinner, TheBasis, p, AffBasis, nbVert, GramMat_Discriminant, TheScal, GRPperm, ListMatrGens, GRPmatr, LDim, BigEXT, ListLinGen, ListTransGen, InnerListMatrGen, AffBas, lenAff, lenVect, iAff, iVect, TotalListMatrGen, eLinMat, TheFirstBasis, TheSecondBasis, TheSecondVectSpace, eGen, eTransMat, nVect, jVect;
  n:=TheDelaunay.n;
  # 
  # first component, the inner generators
  #
  GramMat_Discriminant:=InfDel_GetGramDiscMat(TheDelaunay, TheDelaunay.EXT);
  GRPperm:=AutomorphismGroupColoredGraph(GramMat_Discriminant);
  InnerListMatrGen:=List(GeneratorsOfGroup(GRPperm), x->InfDel_GetEquivalence(TheDelaunay, TheDelaunay, x));
  # 
  # second component, the translations
  #
  AffBas:=CreateAffineBasis(TheDelaunay.EXT);
  lenAff:=Length(AffBas);
  lenVect:=Length(TheDelaunay.VectSpace);
  ListTransGen:=[];
  TheFirstBasis:=Concatenation(AffBas, List(TheDelaunay.VectSpace, x->Concatenation([0], x)));
  for iAff in [1..lenAff]
  do
    for iVect in [1..lenVect]
    do
      TheSecondBasis:=Concatenation(AffBas, List(TheDelaunay.VectSpace, x->Concatenation([0], x)));
      TheSecondBasis[iAff]:=TheSecondBasis[iAff] + Concatenation([0], TheDelaunay.VectSpace[iVect]);
      eTransMat:=TheSecondBasis*Inverse(TheFirstBasis);
      Add(ListTransGen, eTransMat);
    od;
  od;
  # 
  # third component, the general linear operations
  #
  ListLinGen:=[];
  if lenVect>0 then
    for eGen in GeneratorsOfGroup(GL(lenVect, Integers))
    do
      TheSecondVectSpace:=[];
      for iVect in [1..lenVect]
      do
        nVect:=ListWithIdenticalEntries(n,0);
        for jVect in [1..lenVect]
        do
          nVect:=nVect + eGen[jVect][iVect]*TheDelaunay.VectSpace[jVect];
        od;
        Add(TheSecondVectSpace, nVect);
      od;
      TheSecondBasis:=Concatenation(AffBas, List(TheSecondVectSpace, x->Concatenation([0], x)));
      eLinMat:=TheSecondBasis*Inverse(TheFirstBasis);
      Add(ListLinGen, eLinMat);
    od;
  fi;
  TotalListMatrGen:=Concatenation(InnerListMatrGen, ListTransGen, ListLinGen);
  GRPmatr:=Group(TotalListMatrGen);
  return rec(GRPmatr:=GRPmatr, 
             GRPperm:=GRPperm, 
             InnerListMatrGen:=InnerListMatrGen, 
             ListTransGen:=ListTransGen, 
             ListLinGen:=ListLinGen);
end;



InfDel_TestEquivalence:=function(TheDelaunay1, TheDelaunay2)
  local TheM1, TheM2, test, eGen;
  TheM1:=InfDel_GetGramDiscMat(TheDelaunay1,TheDelaunay1.EXT);
  TheM2:=InfDel_GetGramDiscMat(TheDelaunay2,TheDelaunay2.EXT);
  test:=IsIsomorphicColoredGraph(TheM1, TheM2);
  if test=false then
    return false;
  fi;
  eGen:=PermList(test);
  return InfDel_GetEquivalence(TheDelaunay1, TheDelaunay2, eGen);
end;



InfDel_PairStabilizer:=function(TheSuperPolytope, ThePolytope)
  local ListDistMat, TheDistMat, GRPperm, ListMatrGens, RetMatrGRP, ListPermGens, phi;
  if InfDel_IsSubset(ThePolytope, TheSuperPolytope)=false then
    Error("We do not have inclusion, thus we failed in InfDel_PairStabilizer");
  fi;
  ListDistMat:=[];
  Add(ListDistMat, InfDel_GetGramDiscMat(ThePolytope, ThePolytope.EXT));
  Add(ListDistMat, InfDel_GetGramDiscMat(TheSuperPolytope, ThePolytope.EXT));
  TheDistMat:=InfDel_MergeDistMatrices(ListDistMat);
  GRPperm:=AutomorphismGroupColoredGraph(TheDistMat);
  ListPermGens:=GeneratorsOfGroup(GRPperm);
  ListMatrGens:=List(ListPermGens, x->InfDel_GetEquivalence(ThePolytope, ThePolytope, x));
  RetMatrGRP:=Group(ListMatrGens);
  phi:=GroupHomomorphismByImagesNC(GRPperm, RetMatrGRP, ListPermGens, ListMatrGens);
  if InfDel_IsStabilizer(TheSuperPolytope, RetMatrGRP)=false then
    Error("Error on TheSuperPolytope for InfDel_PairStabilizer");
  fi;
  if InfDel_IsStabilizer(ThePolytope, RetMatrGRP)=false then
    Error("Error on ThePolytope for InfDel_PairStabilizer");
  fi;
  return rec(TheMatrGRP:=RetMatrGRP, GRPperm:=GRPperm, phi:=phi);
end;







InfDel_PairEquivalence:=function(TheSuperPolytope, ThePolytope1, ThePolytope2)
  local ListDistMat1, ListDistMat2, TheDistMat1, TheDistMat2, test, eGen, eEquivMatr;
  if InfDel_IsSubset(ThePolytope1, TheSuperPolytope)=false then
    Error("We do not have inclusion, thus we failed in InfDel_PairEquivalence 1");
  fi;
  if InfDel_IsSubset(ThePolytope2, TheSuperPolytope)=false then
    Error("We do not have inclusion, thus we failed in InfDel_PairEquivalence 2");
  fi;
  if Length(ThePolytope1.EXT)<>Length(ThePolytope2.EXT) then
    return false;
  fi;
  if RankMat(ThePolytope1.EXT)<>RankMat(ThePolytope2.EXT) then
    return false;
  fi;
  ListDistMat1:=[];
  Add(ListDistMat1, InfDel_GetGramDiscMat(ThePolytope1, ThePolytope1.EXT));
  Add(ListDistMat1, InfDel_GetGramDiscMat(TheSuperPolytope, ThePolytope1.EXT));
  TheDistMat1:=InfDel_MergeDistMatrices(ListDistMat1);
  ListDistMat2:=[];
  Add(ListDistMat2, InfDel_GetGramDiscMat(ThePolytope2, ThePolytope2.EXT));
  Add(ListDistMat2, InfDel_GetGramDiscMat(TheSuperPolytope, ThePolytope2.EXT));
  TheDistMat2:=InfDel_MergeDistMatrices(ListDistMat2);
  test:=IsIsomorphicColoredGraph(TheDistMat1, TheDistMat2);
  if test=false then
    return false;
  fi;
  eGen:=PermList(test);
  eEquivMatr:=InfDel_GetEquivalence(ThePolytope1, ThePolytope2, eGen);
  if InfDel_IsEquivalence(ThePolytope1, ThePolytope2, eEquivMatr)=false then
    Error("Error at ThePolytope1,2");
  fi;
  if InfDel_IsEquivalence(TheSuperPolytope, TheSuperPolytope, eEquivMatr)=false then
    Error("Error at TheSuperPolytope");
  fi;
  return eEquivMatr;
end;



InfDel_TripleEquivalence:=function(TheSuperDelaunay, TheDelaunay, TheSubDelaunay1, TheSubDelaunay2)
  local ListDistMat1, ListDistMat2, TheDistMat1, TheDistMat2, test, eGen, eEquivMatr;
  if InfDel_IsSubset(TheDelaunay, TheSuperDelaunay)=false then
    Error("We do not have inclusion, thus we failed in InfDel_TripleEquivalence 1");
  fi;
  if InfDel_IsSubset(TheSubDelaunay1, TheDelaunay)=false then
    Error("We do not have inclusion, thus we failed in InfDel_TripleEquivalence 2");
  fi;
  if InfDel_IsSubset(TheSubDelaunay2, TheDelaunay)=false then
    Error("We do not have inclusion, thus we failed in InfDel_TripleEquivalence 3");
  fi;
  if Length(TheSubDelaunay1.EXT)<>Length(TheSubDelaunay2.EXT) then
    return false;
  fi;
  if RankMat(TheSubDelaunay1.EXT)<>RankMat(TheSubDelaunay2.EXT) then
    return false;
  fi;
  ListDistMat1:=[];
  Add(ListDistMat1, InfDel_GetGramDiscMat(TheSubDelaunay1, TheSubDelaunay1.EXT));
  Add(ListDistMat1, InfDel_GetGramDiscMat(TheDelaunay, TheSubDelaunay1.EXT));
  Add(ListDistMat1, InfDel_GetGramDiscMat(TheSuperDelaunay, TheSubDelaunay1.EXT));
  TheDistMat1:=InfDel_MergeDistMatrices(ListDistMat1);
  ListDistMat2:=[];
  Add(ListDistMat2, InfDel_GetGramDiscMat(TheSubDelaunay2, TheSubDelaunay2.EXT));
  Add(ListDistMat2, InfDel_GetGramDiscMat(TheDelaunay, TheSubDelaunay2.EXT));
  Add(ListDistMat2, InfDel_GetGramDiscMat(TheSuperDelaunay, TheSubDelaunay2.EXT));
  TheDistMat2:=InfDel_MergeDistMatrices(ListDistMat2);
  test:=IsIsomorphicColoredGraph(TheDistMat1, TheDistMat2);
  if test=false then
    return false;
  fi;
  eGen:=PermList(test);
  eEquivMatr:=InfDel_GetEquivalence(TheSubDelaunay1, TheSubDelaunay2, eGen);
  if InfDel_IsEquivalence(TheSubDelaunay1, TheSubDelaunay2, eEquivMatr)=false then
    Error("Error at TheSubDelaunay1,2");
  fi;
  if InfDel_IsEquivalence(TheSuperDelaunay, TheSuperDelaunay, eEquivMatr)=false then
    Error("Error at TheSuperDelaunay");
  fi;
  if InfDel_IsEquivalence(TheDelaunay, TheDelaunay, eEquivMatr)=false then
    Error("Error at TheDelaunay");
  fi;
  return eEquivMatr;
end;


InfDel_GetEffectiveRank:=function(TheDelaunay)
  local VectSpaceExt;
  VectSpaceExt:=List(TheDelaunay.VectSpace, x->Concatenation([0], x));
  return RankMat(Concatenation(TheDelaunay.EXT, VectSpaceExt));
end;

InfDel_GetLinearSpace:=function(TheDelaunay)
  local n, LinEXT, TheBasis, AffBasis, p, BigEXT, BigEXTred, TheNewBasis, eBigMat, i, j, eNewMat, eMat;
  n:=TheDelaunay.n;
  LinEXT:=InfDel_GetLinSpaceFromPolytope(TheDelaunay.EXT);
  TheBasis:=Concatenation(LinEXT, TheDelaunay.VectSpace);
  AffBasis:=InfDel_GetAffineBasis(TheBasis);
  p:=Length(LinEXT);
  BigEXT:=TheDelaunay.EXT*Inverse(AffBasis);
  BigEXTred:=List(BigEXT, x->x{[1..p+1]});
  TheBasis:=GetRankBasisPolytope(BigEXTred);
  TheNewBasis:=[];
  for eMat in TheBasis
  do
    eBigMat:=NullMat(n+1,n+1);
    for i in [1..p+1]
    do
      for j in [1..p+1]
      do
        eBigMat[i][j]:=eMat[i][j];
      od;
    od;
    eNewMat:=Inverse(AffBasis)*eBigMat*TransposedMat(Inverse(AffBasis));
    Add(TheNewBasis, eNewMat);
  od;
  return TheNewBasis;
end;

InfDel_GetLinearSpaceIntegral:=function(TheDelaunay)
  local n, FuncIndex, ListEqua, eVect, j, i, eSet, eEqua, eVert, NSP, TheLinSpace, eNSP, eMat;
  n:=TheDelaunay.n;
  FuncIndex:=function(i,j)
    return (i-1)*(n+1)+j;
  end;
  ListEqua:=[];
  for eVect in TheDelaunay.VectSpace
  do
    for j in [1..n+1]
    do
      eEqua:=ListWithIdenticalEntries((n+1)*(n+1),0);
      for i in [1..n]
      do
        eEqua[FuncIndex(i+1,j)]:=eVect[i];
      od;
      Add(ListEqua, eEqua);
    od;
  od;
  for eSet in Combinations([1..n+1],2)
  do
    i:=eSet[1];
    j:=eSet[2];
    eEqua:=ListWithIdenticalEntries((n+1)*(n+1),0);
    eEqua[FuncIndex(i,j)]:=1;
    eEqua[FuncIndex(j,i)]:=-1;
    Add(ListEqua, eEqua);
  od;
  for eVert in TheDelaunay.EXT
  do
    eEqua:=ListWithIdenticalEntries((n+1)*(n+1),0);
    for i in [1..n+1]
    do
      for j in [1..n+1]
      do
        eEqua[FuncIndex(i,j)]:=eVert[i]*eVert[j];
      od;
    od;
    Add(ListEqua, eEqua);
  od;
  NSP:=NullspaceIntMat(TransposedMat(ListEqua));
  TheLinSpace:=[];
  for eNSP in NSP
  do
    eMat:=[];
    for i in [1..n+1]
    do
      Add(eMat, eNSP{[1+(i-1)*(n+1)..i*(n+1)]});
    od;
    if TransposedMat(eMat)<>eMat then
      Error("Non symmetric matrix, This is not allowed");
    fi;
    Add(TheLinSpace, eMat);
  od;
  return TheLinSpace;
end;

InfDel_L1Norm:=function(eMat)
  local eSum, eLine, eVal;
  eSum:=0;
  for eLine in eMat
  do
    for eVal in eLine
    do
      eSum:=eSum+AbsInt(eVal);
    od;
  od;
  return eSum;
end;

InfDel_HeuristicSimplification:=function(eQuadFunction)
  local TheZerSet, TheLinSpaceInt, TheLinSpaceWork, WorkQuadFunc, PrevNormL1, WeFindSomething, eMat, NewMat, NewNormL1, NewZer, TheReply;
  TheZerSet:=InfDel_GetZeroSet(eQuadFunction);
  TheLinSpaceInt:=InfDel_GetLinearSpaceIntegral(TheZerSet);
  TheLinSpaceWork:=Concatenation(TheLinSpaceInt, List(TheLinSpaceInt, x->-x));
  WorkQuadFunc:=List(eQuadFunction, x->x);
  PrevNormL1:=InfDel_L1Norm(WorkQuadFunc);
  while(true)
  do
    WeFindSomething:=false;
    for eMat in TheLinSpaceWork
    do
      if WeFindSomething=false then
        NewMat:=WorkQuadFunc + eMat;
        NewNormL1:=InfDel_L1Norm(NewMat);
        if NewNormL1 < PrevNormL1 then
          TheReply:=InfDel_GetZeroSetKernel(NewMat);
          if IsBound(TheReply.error)=false then
            if InfDel_IsEqual(TheReply.TheRec, TheZerSet)=true then
              WeFindSomething:=true;
              WorkQuadFunc:=NewMat;
#              Print("PrevNormL1=", PrevNormL1, " NewNormL1=", NewNormL1, "\n");
              PrevNormL1:=NewNormL1;
            fi;
          fi;
        fi;
      fi;
    od;
    if WeFindSomething=false then
      break;
    fi;
  od;
  return WorkQuadFunc;
end;



InfDel_GetAdjacentVertices:=function(TheDelaunay)
  local n, SPC, p, p2, TheBasis, AffBasis, NewEXT, NewQuadForm, ListRelVert, EXT2, TheQuad2, DistMat, eGen, eMatrGen, GRP2;
  n:=TheDelaunay.n;
  SPC:=InfDel_GetLinSpaceFromPolytope(TheDelaunay.EXT);
  p:=Length(SPC);
  p2:=Length(TheDelaunay.VectSpace);
  TheBasis:=Concatenation(SPC, TheDelaunay.VectSpace);
  AffBasis:=InfDel_GetAffineBasis(TheBasis);
  NewEXT:=TheDelaunay.EXT*Inverse(AffBasis);
  NewQuadForm:=TheBasis*TheDelaunay.TheQuadForm*TransposedMat(TheBasis);
  EXT2:=List(NewEXT, x->x{[1..p+1]});
  TheQuad2:=List(NewQuadForm{[1..p]}, x->x{[1..p]});
  DistMat:=DistanceMatrixDelaunay(TheQuad2, EXT2);
  GRP2:=AutomorphismGroupEdgeColoredGraph(DistMat);
  for eGen in GeneratorsOfGroup(GRP2)
  do
    eMatrGen:=FindTransformation(EXT2, EXT2, eGen);
    if IsIntegralMat(eMatrGen)=false then
      Error("We need to work some more");
    fi;
  od;
  ListRelVert:=GetVerticesAdjacentDelaunay(TheQuad2, EXT2, GRP2);
  return List(ListRelVert, x->Concatenation(x, ListWithIdenticalEntries(p2, 0)))*AffBasis;
end;




InfDel_GetNegVector:=function(eQuadFunc)
  local eQuadForm, n, TheINF, pos, eNegVect, i, eVect;
  eQuadForm:=InfDel_GetQuadForm(eQuadFunc);
  n:=Length(eQuadForm);
  TheINF:=DiagonalizeSymmetricMatrix(eQuadForm);
  pos:=First([1..n], x->TheINF.RedMat[x][x]<0);
  eNegVect:=RemoveFraction(TheINF.Transform[pos]);
  i:=1;
  while(true)
  do
    eVect:=Concatenation([1], i*eNegVect);
    if eVect*eQuadFunc*eVect < 0 then
      return eVect;
    fi;
    i:=i+1;
  od;
end;


InfDel_GetCanonicalPosQuadFuncExpression:=function(TheRec)
  local n, TheSPC, p, TheBasis, AffBasis, NewRec, NewEXT, NewListAdjacentVert, WorkListAdjacent, WorkListAdjacentSel, ReduceFunction, TheQuadFuncRed, ListAdditionalVertices, GRPmatr, ListIneq, ToBeMinimized, TheFunc, eVert, eList, TheLP, eVect, i, j, TheDiff, BigPosQuadFunc, TheReply, eEnt, pLin, TheLinSpaceRed, TheLinSpace, TheNewFunc, TheNewQuad, NewRec2, CongrGRP, WorkListAdjacentVert, LFC, WeComputedDelaunayTessel, ListFunc;
  ReduceFunction:=function(eQuad)
    return List(eQuad{[1..p+1]}, x->x{[1..p+1]});
  end;
  n:=TheRec.n;
  TheSPC:=InfDel_GetLinSpaceFromPolytope(TheRec.EXT);
  p:=Length(TheSPC);
  TheBasis:=Concatenation(TheSPC, TheRec.VectSpace);
  AffBasis:=InfDel_GetAffineBasis(TheBasis);
  NewRec:=InfDel_AffineTransformation(TheRec, AffBasis);
  NewEXT:=List(NewRec.EXT, x->x{[1..p+1]});
  GRPmatr:=InfDel_Stabilizer(rec(n:=p, EXT:=NewEXT, VectSpace:=[])).GRPmatr;
  CongrGRP:=Group(List(GeneratorsOfGroup(GRPmatr), TransposedMat));
  TheQuadFuncRed:=ReduceFunction(NewRec.TheQuadFunction);
  TheNewFunc:=RemoveFractionMatrix(OrbitBarycenterSymmetricMatrix(TheQuadFuncRed, CongrGRP));
  TheNewQuad:=InfDel_GetQuadForm(TheNewFunc);
  NewRec2:=rec(n:=n, EXT:=NewEXT, VectSpace:=[], TheQuadFunction:=TheNewFunc, TheQuadForm:=TheNewQuad);
  WorkListAdjacentVert:=InfDel_GetAdjacentVertices(NewRec2);
  WorkListAdjacentSel:=Filtered(WorkListAdjacentVert, x->Position(NewEXT, x)=fail);
  TheLinSpace:=InfDel_GetLinearSpace(NewRec);
  pLin:=Length(TheLinSpace);
  TheLinSpaceRed:=List(TheLinSpace, ReduceFunction);
  ListAdditionalVertices:=[];
  Print("|GRPmatr|=", Order(GRPmatr), "\n");
  WeComputedDelaunayTessel:=false;
  while(true)
  do
    ListIneq:=[];
    ToBeMinimized:=ListWithIdenticalEntries(pLin+1,0);
    for eVert in Concatenation(WorkListAdjacentSel, ListAdditionalVertices)
    do
      eList:=Concatenation([-1], List(TheLinSpaceRed, x->eVert*x*eVert));
      Add(ListIneq, eList);
      ToBeMinimized:=ToBeMinimized+eList;
    od;
    TheLP:=LinearProgramming(ListIneq, ToBeMinimized);
    if IsBound(TheLP.primal_solution)=false then
      Error("No solution found, please panic");
    fi;
    eVect:=ListWithIdenticalEntries(pLin, 0);
    for eEnt in TheLP.primal_solution
    do
      eVect[eEnt[1]]:=eEnt[2];
    od;
    TheFunc:=NullMat(p+1,p+1);
    for i in [1..pLin]
    do
      TheFunc:=TheFunc+eVect[i]*TheLinSpaceRed[i];
    od;
    TheReply:=InfDel_GetZeroSetKernel(RemoveFractionMatrix(TheFunc));
    if IsBound(TheReply.error)=true or Length(TheReply.TheRec.VectSpace)>0 or Set(TheReply.TheRec.EXT)<>Set(NewEXT) then
      if WeComputedDelaunayTessel=false then
        ListFunc:=DelaunayComputationStandardFunctions(TheNewQuad);
        LFC:=ListFunc.GetNeighborhood(NewEXT);
        LFC.DoIncrement();
        WeComputedDelaunayTessel:=true;
      fi;
      LFC.DoIncrement();
      ListAdditionalVertices:=LFC.GetAllAddedVertices();
    else
      break;
    fi;
    Print("|ListAdditionalVertices|=", Length(ListAdditionalVertices), "\n");
  od;
  BigPosQuadFunc:=NullMat(n+1,n+1);
  for i in [1..p+1]
  do
    for j in [1..p+1]
    do
      BigPosQuadFunc[i][j]:=TheFunc[i][j];
    od;
  od;
  return RemoveFractionMatrix(Inverse(AffBasis)*BigPosQuadFunc*TransposedMat(Inverse(AffBasis)));
end;



InfDel_GetLocalCone:=function(TheRec)
  local n, TheSPC, p, TheBasis, AffBasis, NewRec, NewEXT, NewListAdjacentVert, WorkListAdjacent, WorkListAdjacentSel, ReduceFunction, TheQuadFuncRed, ListAdditionalVertices, GRPmatr, ListIneq, ToBeMinimized, TheFunc, eVert, eList, TheLP, eVect, i, j, TheDiff, BigPosQuadFunc, TheReply, eEnt, pLin, TheLinSpaceRed, TheLinSpace, TheNewFunc, TheNewQuad, NewRec2, CongrGRP, WorkListAdjacentVert, GetOutsideVectOnZero, LFC, WeComputedDelaunayTessel, ListFunc, ProvisionaryListRelevant, NeedToIterate, eQuadFunc, ListOrbitQuadFuncRed, eEXT, GRPperm, EXT, ListPermGens, TotalListVert, TheStab, ListOrbitSubpolytope, eNewFunc, eGen, eIneq;
  ReduceFunction:=function(eQuad)
    return List(eQuad{[1..p+1]}, x->x{[1..p+1]});
  end;
  n:=TheRec.n;
  TheSPC:=InfDel_GetLinSpaceFromPolytope(TheRec.EXT);
  p:=Length(TheSPC);
  TheBasis:=Concatenation(TheSPC, TheRec.VectSpace);
  AffBasis:=InfDel_GetAffineBasis(TheBasis);
  NewRec:=InfDel_AffineTransformation(TheRec, AffBasis);
  NewEXT:=List(NewRec.EXT, x->x{[1..p+1]});
  TheStab:=InfDel_Stabilizer(rec(n:=p, EXT:=NewEXT, VectSpace:=[]));
  GRPmatr:=TheStab.GRPmatr;
  CongrGRP:=Group(List(GeneratorsOfGroup(GRPmatr), TransposedMat));
  TheQuadFuncRed:=ReduceFunction(NewRec.TheQuadFunction);
  TheNewFunc:=RemoveFractionMatrix(OrbitBarycenterSymmetricMatrix(TheQuadFuncRed, CongrGRP));
  TheNewQuad:=InfDel_GetQuadForm(TheNewFunc);
  NewRec2:=rec(n:=n, EXT:=NewEXT, VectSpace:=[], TheQuadFunction:=TheNewFunc, TheQuadForm:=TheNewQuad);
  WorkListAdjacentVert:=InfDel_GetAdjacentVertices(NewRec2);
  ProvisionaryListRelevant:=Filtered(WorkListAdjacentVert, x->Position(NewEXT, x)=fail);
  TheLinSpace:=InfDel_GetLinearSpace(NewRec);
  pLin:=Length(TheLinSpace);
  TheLinSpaceRed:=List(TheLinSpace, ReduceFunction);
  ListAdditionalVertices:=[];
  Print("|GRPmatr|=", Order(GRPmatr), "\n");
  WeComputedDelaunayTessel:=false;
  ListOrbitQuadFuncRed:=[];
  while(true)
  do
    ListIneq:=[];
    TotalListVert:=Concatenation(WorkListAdjacentSel, ListAdditionalVertices);
    for eVert in ProvisionaryListRelevant
    do
      eIneq:=List(TheLinSpaceRed, x->eVert*x*eVert);
      Add(ListIneq, eIneq);
    od;
    ListPermGens:=[];
    for eGen in GeneratorsOfGroup(TheStab.GRPmatr)
    do
      eList:=List(TotalListVert, x->Position(TotalListVert, x*eGen));
      Add(ListPermGens, PermList(eList));
    od;
    GRPperm:=Group(ListPermGens);
    EXT:=DualDescriptionStandard(ListIneq, GRPperm);
    NeedToIterate:=false;
    for eEXT in EXT
    do
      eQuadFunc:=NullMat(p+1, p+1);
      for i in [1..p+1]
      do
        eQuadFunc:=eQuadFunc + eEXT[i]*TheLinSpaceRed[i];
      od;
      Add(ListOrbitQuadFuncRed, eQuadFunc);
      TheReply:=InfDel_GetZeroSetKernel(RemoveFractionMatrix(eQuadFunc));
      if IsBound(TheReply.error)=true or InfDel_IsSubset(NewRec2, TheReply.TheRec)=false then
        NeedToIterate:=true;
      fi;
    od;
    if NeedToIterate=true then
      if WeComputedDelaunayTessel=false then
        ListFunc:=DelaunayComputationStandardFunctions(TheNewQuad);
        LFC:=ListFunc.GetNeighborhood(NewEXT);
        LFC.DoIncrement();
        WeComputedDelaunayTessel:=true;
      fi;
      LFC.DoIncrement();
      ProvisionaryListRelevant:=LFC.GetAllAddedVertices();
    else
      break;
    fi;
    Print("|ProvisionaryListRelevant|=", Length(ProvisionaryListRelevant), "\n");
  od;
  ListOrbitSubpolytope:=[];
  for TheFunc in ListOrbitQuadFuncRed
  do
    BigPosQuadFunc:=NullMat(n+1,n+1);
    for i in [1..p+1]
    do
      for j in [1..p+1]
      do
        BigPosQuadFunc[i][j]:=TheFunc[i][j];
      od;
    od;
    eNewFunc:=RemoveFractionMatrix(Inverse(AffBasis)*BigPosQuadFunc*TransposedMat(Inverse(AffBasis)));
    Add(ListOrbitSubpolytope, InfDel_GetZeroSetKernel(eNewFunc));
  od;
  return ListOrbitSubpolytope;
end;




InfDel_LtypeSimplification:=function(TheRec)
  local n, ReduceFunction, TheSPC, p, TheBasis, AffBasis, NewRec, NewEXT, GRPmatr, CongrGRP, TheQuadFuncRed, TheNewFunc, TheNewQuad, TheLinSpace, pLin, TheLinSpaceRed, eCase, eVect, TheReply, TheRecRed, TheFunc, i, ListIneq, TheFuncInt,  TheBigFunc, TheRetFunc, j, TheLinSpaceInt, TheLinSpaceWork, NewFunc, TheWorkQuad, TheQuadFormRed, TheGRP, TheSymmSpace, GRPrec, TheLinSpaceRedExpand, TheNewFuncExpand, GetFromFullSymm, GetRandom;
  n:=TheRec.n;
  ReduceFunction:=function(eQuad)
    return List(eQuad{[1..p+1]}, x->x{[1..p+1]});
  end;
  TheSPC:=InfDel_BasisCompletion(TheRec.VectSpace, IdentityMat(n), n);
  p:=Length(TheSPC);
  TheBasis:=Concatenation(TheSPC, TheRec.VectSpace);
  AffBasis:=InfDel_GetAffineBasis(TheBasis);
  NewRec:=InfDel_AffineTransformation(TheRec, AffBasis);
  NewEXT:=List(NewRec.EXT, x->x{[1..p+1]});
  TheRecRed:=rec(n:=p, EXT:=NewEXT, VectSpace:=[]);
  GRPrec:=InfDel_Stabilizer(TheRecRed);
  GRPmatr:=GRPrec.GRPmatr;
  Print("Ltype Simpl |GRPperm|=", Order(GRPrec.GRPperm), "\n");
  CongrGRP:=Group(List(GeneratorsOfGroup(GRPmatr), TransposedMat));
  TheQuadFuncRed:=ReduceFunction(NewRec.TheQuadFunction);
  TheQuadFormRed:=InfDel_GetQuadForm(TheQuadFuncRed);
  TheNewFunc:=RemoveFractionMatrix(OrbitBarycenterSymmetricMatrix(TheQuadFuncRed, CongrGRP));
  TheNewFuncExpand:=SymmetricMatrixToVector(TheNewFunc);
  TheNewQuad:=InfDel_GetQuadForm(TheNewFunc);
  #
  TheLinSpaceRed:=InfDel_GetLinearSpace(TheRecRed);
  TheLinSpaceInt:=InfDel_GetLinearSpaceIntegral(TheRecRed);
  TheLinSpaceWork:=Concatenation(TheLinSpaceInt, List(TheLinSpaceInt, x->-x));
  TheLinSpaceRedExpand:=List(TheLinSpaceRed, SymmetricMatrixToVector);
  if SolutionMat(TheLinSpaceRedExpand, TheNewFuncExpand)=fail then
    Error("Incorrection somewhere");
  fi;
  pLin:=Length(TheLinSpaceRed);
  eCase:=rec(Basis:=List(TheLinSpaceRed, InfDel_GetQuadForm), SuperMat:=TheQuadFormRed);
  TheSymmSpace:=FindFullSymmetrySpace(eCase);
  GetRandom:=function()
    local NewFunc, TheReply, TheWorkFunc, TheWorkQuad, ListFunc, TheDelCO, TheRigid, TheGRP, TheDelCOsmall, FAC, ToBeMinimized, ListIneq, eFac, eIneq, TheLP, eVect, eEnt;
    TheWorkFunc:=TheQuadFuncRed;
    while(true)
    do
      NewFunc:=TheWorkFunc + Random(TheLinSpaceWork);
      TheReply:=InfDel_GetZeroSetKernel(NewFunc);
      if IsBound(TheReply.error)=false then
        if InfDel_IsEqual(TheReply.TheRec, TheRecRed)=true then
          TheWorkFunc:=NewFunc;
          TheWorkQuad:=InfDel_GetQuadForm(TheWorkFunc);
          ListFunc:=DelaunayComputationStandardFunctions(TheWorkQuad);
          TheDelCO:=ListFunc.GetDelaunayDescription();
          TheRigid:=RigidityDegree(TheDelCO, eCase);
          TheGRP:=ListFunc.GetMatrixGroup();
          if IsSubset(TheGRP, TheSymmSpace)=false then
            Error("We have a serious error");
          fi;
          Print("Rigidity degree=", TheRigid, "   |TheGRP|=", Order(TheGRP), "  |TheSymmSpace|=", Order(TheSymmSpace), "\n");
          if TheRigid=Length(eCase.Basis) then
            break;
          fi;
        fi;
      fi;
    od;
    Print("Exiting loop after success\n");
    TheDelCOsmall:=SymmetryBreakingDelaunayDecomposition(TheDelCO, TheGRP, TheSymmSpace, ListFunc.GetInvariantBasis());
    FAC:=WriteFaceInequalities(TheDelCOsmall, eCase);
    ToBeMinimized:=ListWithIdenticalEntries(pLin+1,0);
    ListIneq:=[];
    for eFac in FAC.ListInequalities
    do
      eIneq:=Concatenation([-1], eFac{[2..pLin+1]});
      Add(ListIneq, eIneq);
      ToBeMinimized:=ToBeMinimized+eIneq;
    od;
    TheLP:=LinearProgramming(ListIneq, ToBeMinimized);
    if IsBound(TheLP.primal_solution)=false then
      Error("No solution found, please panic");
    fi;
    eVect:=ListWithIdenticalEntries(pLin, 0);
    for eEnt in TheLP.primal_solution
    do
      eVect[eEnt[1]]:=eEnt[2];
    od;
    return eVect;
  end;
  GetFromFullSymm:=function()
    local ListFunc, TheDelCO, TheGRP, TheDelCOsmall, FAC, ToBeMinimized, ListIneq, eFac, eIneq, TheLP, eVect, eEnt, NSP, ListEqualities, ListEqualitiesRed, eFacRed, eOrb;
    ListFunc:=DelaunayComputationStandardFunctions(TheQuadFormRed);
    TheDelCO:=ListFunc.GetDelaunayDescription();
    TheGRP:=ListFunc.GetMatrixGroup();
    if IsSubset(TheGRP, TheSymmSpace)=false then
      Error("We have a serious error");
    fi;
    TheDelCOsmall:=SymmetryBreakingDelaunayDecomposition(TheDelCO, TheGRP, TheSymmSpace, ListFunc.GetInvariantBasis());
    ListEqualities:=[];
    for eOrb in TheDelCOsmall
    do
      Append(ListEqualities, ListEqualitiesDelaunay(eOrb.EXT, eCase.Basis));
    od;
    ListEqualitiesRed:=List(ListEqualities, x->x{[2..pLin+1]}); 
    if Length(ListEqualitiesRed)=0 then
      NSP:=IdentityMat(pLin);
    else
      NSP:=NullspaceMat(TransposedMat(ListEqualitiesRed));
    fi;
    FAC:=WriteFaceInequalities(TheDelCOsmall, eCase);
    ToBeMinimized:=ListWithIdenticalEntries(pLin+1,0);
    ListIneq:=[];
    for eFac in FAC.ListInequalities
    do
      eFacRed:=eFac{[2..pLin+1]};
      eIneq:=Concatenation([-1], List(NSP, x->x*eFacRed));
      Add(ListIneq, eIneq);
      ToBeMinimized:=ToBeMinimized+eIneq;
    od;
    TheLP:=LinearProgramming(ListIneq, ToBeMinimized);
    if IsBound(TheLP.primal_solution)=false then
      Error("No solution found, please panic");
    fi;
    eVect:=ListWithIdenticalEntries(Length(NSP), 0);
    for eEnt in TheLP.primal_solution
    do
      eVect[eEnt[1]]:=eEnt[2];
    od;
    return NSP*eVect;
  end;
  Print("Print LP solved correctly\n");
  Print("n=", n, "  p=", p, "\n");
  eVect:=GetRandom();
#  eVect:=GetFromFullSymm();
  TheFunc:=NullMat(p+1,p+1);
  for i in [1..pLin]
  do
    TheFunc:=TheFunc+eVect[i]*TheLinSpaceRed[i];
  od;
  TheFuncInt:=RemoveFractionMatrix(TheFunc);
  TheBigFunc:=NullMat(n+1,n+1);
  for i in [1..p+1]
  do
    for j in [1..p+1]
    do
      TheBigFunc[i][j]:=TheFuncInt[i][j];
    od;
  od;
  TheRetFunc:=Inverse(AffBasis)*TheBigFunc*TransposedMat(Inverse(AffBasis));
  TheReply:=InfDel_GetZeroSetKernel(TheRetFunc);
  if IsBound(TheReply.error)=true then
    Error("There is an error, please panic");
  fi;
  if InfDel_IsEqual(TheReply.TheRec, TheRec)=false then
    Error("There is an error, please panic 3");
  fi;
  return TheRetFunc;
end;








#
#
# search for negative vector in TheDelaunay
InfDel_GetNegCVPVector:=function(NewQuadFunction, TheDelaunay)
  local n, eEXT, TheBasis, AffBasis, RenormQuadFunction, renormEXT, RedQuadForm, TheQuadFunc, TheSideMat, eRenEXT, eEXTred, TheSQR, cCentRed, TheCVP, eNewEXT, eVal, p1, p2, p3diff, SPC1, SPC2, NSP, NewQuadForm, NSPsub, NSPcpl, ListEqua1, ListEqua2;
  n:=TheDelaunay.n;
  if Length(TheDelaunay.VectSpace)=0 then
    ListEqua1:=IdentityMat(n);
  else
    ListEqua1:=NullspaceIntMat(TransposedMat(TheDelaunay.VectSpace));
  fi;
  NewQuadForm:=InfDel_GetQuadForm(NewQuadFunction);
  NSP:=NullspaceIntMat(NewQuadForm);
  if Length(NSP)=0 then
    ListEqua2:=IdentityMat(n);
  else
    ListEqua2:=NullspaceIntMat(TransposedMat(NSP));
  fi;
  NSPsub:=NullspaceIntMat(TransposedMat(Concatenation(ListEqua1, ListEqua2)));
  SPC1:=InfDel_BasisCompletion(NSPsub, TheDelaunay.VectSpace, n);
  NSPcpl:=InfDel_BasisCompletion(NSPsub, NSP, n);
  SPC2:=InfDel_BasisCompletion(Concatenation(NSPsub, SPC1), IdentityMat(n), n);
  TheBasis:=Concatenation(SPC2, SPC1, NSPsub);
  AffBasis:=InfDel_GetAffineBasis(TheBasis);
  p1:=Length(SPC2);
  p2:=Length(SPC2)+Length(SPC1);
  if p1=p2 then
    for eEXT in TheDelaunay.EXT
    do
      if eEXT*NewQuadFunction*eEXT< 0 then
        return rec(ListVect:=[eEXT], TheResult:=false);
      fi;
    od;
    return rec(TheResult:=true);
  fi;
  p3diff:=Length(NSPsub);
  RenormQuadFunction:=AffBasis*NewQuadFunction*TransposedMat(AffBasis);
  renormEXT:=TheDelaunay.EXT*Inverse(AffBasis);
  RedQuadForm:=List(RenormQuadFunction{[p1+2..p2+1]}, x->x{[p1+2..p2+1]});
  TheQuadFunc:=List(RenormQuadFunction{[1..p1+1]}, x->x{[1..p1+1]});
  TheSideMat:=List(RenormQuadFunction{[1..p1+1]}, x->x{[p1+2..p2+1]});
  for eRenEXT in renormEXT
  do
    eEXTred:=eRenEXT{[1..p1+1]};
    TheSQR:=eEXTred*TheQuadFunc*eEXTred;
    cCentRed:=-eEXTred*TheSideMat*Inverse(RedQuadForm);
    TheCVP:=CVPVallentinProgram(RedQuadForm, cCentRed);
    eNewEXT:=Concatenation(eEXTred, TheCVP.ListVect[1], ListWithIdenticalEntries(p3diff, 0));
    eVal:=eNewEXT*RenormQuadFunction*eNewEXT;
    if eVal<0 then
      return rec(ListVect:=[eNewEXT*AffBasis], TheResult:=false);
    fi;
  od;
  return rec(TheResult:=true);
end;


InfDel_GetEigenRationalConditions:=function(PosQuad1, PosQuad2, SPC)
  local n, wMat1, wMat2, NSP, SPCcpl, wMatRed1, wMatRed2, QMat, ListEig, ListVect, eEig, nMat, p;
  if Length(SPC)=0 then
    return [];
  fi;
  n:=Length(PosQuad1);
  p:=Length(SPC);
  wMat1:=SPC*(2*PosQuad1+PosQuad2)*TransposedMat(SPC);
  wMat2:=SPC*(PosQuad1+2*PosQuad2)*TransposedMat(SPC);
  NSP:=NullspaceIntMat(wMat1);
  SPCcpl:=InfDel_BasisCompletion(NSP, IdentityMat(p), p);
  if Length(SPCcpl)=0 then
    return [];
  fi;
  wMatRed1:=SPCcpl*wMat1*TransposedMat(SPCcpl);
  wMatRed2:=SPCcpl*wMat2*TransposedMat(SPCcpl);
  QMat:=wMatRed2*Inverse(wMatRed1);
  ListEig:=Eigenvalues(Rationals, QMat);
  ListVect:=[];
  for eEig in ListEig
  do
    nMat:=RemoveFractionMatrix(-eEig*wMat1+wMat2);
    Append(ListVect, List(NullspaceIntMat(nMat), x->Concatenation([0], x*SPC)));
  od;
  Print("|ListEig|=", Length(ListEig), " |ListVect|=", Length(ListVect), "\n");
  return ListVect;
end;


InfDel_IsVertexInDelaunay:=function(eVert, TheDelaunay)
  local n, pos, eEXT, eSol;
  n:=TheDelaunay.n;
  if Length(TheDelaunay.VectSpace)=0 then
    pos:=Position(TheDelaunay.EXT, eVert);
    if pos=fail then
      return false;
    else
      return true;
    fi;
  fi;
  for eEXT in TheDelaunay.EXT
  do
    eSol:=SolutionMat(TheDelaunay.VectSpace, eEXT{[2..n+1]} - eVert{[2..n+1]});
    if eSol<>fail then
      return true;
    fi;
  od;
  return false;
end;

InfDel_GetVertexRandomPoint:=function(TheDelaunay, eSiz)
  local n, p, eVert, i;
  n:=TheDelaunay.n;
  p:=Length(TheDelaunay.VectSpace);
  eVert:=Random(TheDelaunay.EXT);
  for i in [1..p]
  do
    eVert:=eVert+Random([-eSiz..eSiz])*Concatenation([0], TheDelaunay.VectSpace[i]);
  od;
  return eVert;
end;



InfDel_GetDefiningAdjacentVertices:=function(TheDelaunay1, TheDelaunay2)
  local n, PreNewDelaunay2, dim1, SPC2, dim2, TheBasis, SPC3, dim3, NewDelaunay1, NewDelaunay2, PosQuad1new, PosQuad2new, BigPosQuad1new, BigPosQuad2new, B22, B32, b, b2, b3, GetFullVector, ListFoundVertices, eVertAdj, eVertAdj2, eVertAdj3, eVertAdj4, eVertAdj5, eVertAdj6, eSubset, AffBasis;
  n:=TheDelaunay1.n;
  PreNewDelaunay2:=InfDel_RewriteCoordinate(TheDelaunay2, TheDelaunay1);
  dim1:=Length(TheDelaunay1.VectSpace);
  SPC2:=InfDel_BasisCompletion(TheDelaunay1.VectSpace,PreNewDelaunay2.VectSpace,n);
  dim2:=Length(SPC2);
  TheBasis:=Concatenation(TheDelaunay1.VectSpace, SPC2);
  SPC3:=InfDel_BasisCompletion(TheBasis, IdentityMat(n), n);
  TheBasis:=Concatenation(TheBasis, SPC3);
  dim3:=n - dim1 - dim2;
  AffBasis:=InfDel_GetAffineBasis(TheBasis);
  # f1=PosQuad1 and f2=PosQuad2
  NewDelaunay1:=InfDel_AffineTransformation(TheDelaunay1, AffBasis);
  NewDelaunay2:=InfDel_AffineTransformation(PreNewDelaunay2, AffBasis);
  PosQuad1new:=NewDelaunay1.TheQuadForm;
  PosQuad2new:=NewDelaunay2.TheQuadForm;
  BigPosQuad1new:=NewDelaunay1.TheQuadFunction;
  BigPosQuad2new:=NewDelaunay2.TheQuadFunction;
  B22:=List(PosQuad1new{[dim1+1..dim1+dim2]}, x->x{[dim1+1..dim1+dim2]});
  B32:=List(PosQuad1new{[dim1+dim2+1..n]}, x->x{[dim1+1..dim1+dim2]});
  b:=BigPosQuad1new[1]{[2..n+1]};
  b2:=b{[dim1+1..dim1+dim2]};
  GetFullVector:=function(w)
    local c, TheCVP, TheVect;
    if Length(B22)=0 then
      return Concatenation([1], ListWithIdenticalEntries(dim1, 0), w);
    fi;
    c:=-(w*B32+b2)*Inverse(B22);
    TheCVP:=CVPVallentinProgram(B22, c);
    return Concatenation([1], ListWithIdenticalEntries(dim1, 0), TheCVP.ListVect[1], w);
  end;
  eSubset:=Concatenation([1], [dim1+dim2+2..n+1]);
  ListFoundVertices:=[];
  for eVertAdj2 in NewDelaunay2.ListAdjacentVert
  do
    eVertAdj3:=eVertAdj2{eSubset};
    eVertAdj4:=eVertAdj3{[2..dim3+1]};
    eVertAdj5:=GetFullVector(eVertAdj4);
    eVertAdj6:=eVertAdj5*AffBasis;
    Add(ListFoundVertices, eVertAdj6);
  od;
  return ListFoundVertices;
end;

InfDel_MaxCoeff:=function(eQuad)
  local TheMaxVal, n, i, j;
  TheMaxVal:=0;
  n:=Length(eQuad);
  for i in [1..n]
  do
    for j in [1..n]
    do
      TheMaxVal:=Maximum(TheMaxVal, AbsInt(eQuad[i][j]));
    od;
  od;
  return TheMaxVal;
end;

InfDel_LiftingDelaunay:=function(TheDelaunay1, TheDelaunay2, TheDelaunay3)
  local LinSpace1, LinSpace2, LinSpace3, n, TheCVP, NewQuadForm, TheNewEXT, i, NewQuadFunction, FuncLift, TheRec, ListInfiniteDirection, sizExt, ListDefinitionVertices, ListRelVertAdja, ListCVPvertices, TheNewRec, TheNewQuadFunction, TheNewQuadForm;
  if InfDel_IsSubset(TheDelaunay1, TheDelaunay2)=false then
    Error("Lifting: Failure of inclusion property 1");
  fi;
  if InfDel_IsSubset(TheDelaunay2, TheDelaunay3)=false then
    Error("Lifting: Failure of inclusion property 2");
  fi;
  LinSpace1:=InfDel_GetLinearSpace(TheDelaunay1);
  LinSpace2:=InfDel_GetLinearSpace(TheDelaunay2);
  LinSpace3:=InfDel_GetLinearSpace(TheDelaunay3);
  n:=TheDelaunay1.n;
  Print("n=", n, 
        " |LinSpace|=", Length(LinSpace1), " ", Length(LinSpace2), " ", Length(LinSpace3), 
        " EffRank=", InfDel_GetEffectiveRank(TheDelaunay1), " ", InfDel_GetEffectiveRank(TheDelaunay2), " ", InfDel_GetEffectiveRank(TheDelaunay3), 
        " |EXT|=", Length(TheDelaunay1.EXT), " ", Length(TheDelaunay2.EXT), " ", Length(TheDelaunay3.EXT), 
        " dim(VectSpace)=", Length(TheDelaunay1.VectSpace), " ", Length(TheDelaunay2.VectSpace), " ", Length(TheDelaunay3.VectSpace), 
        "\n");
  ListRelVertAdja:=Filtered(InfDel_GetDefiningAdjacentVertices(TheDelaunay1, TheDelaunay2), x->InfDel_IsVertexInDelaunay(x, TheDelaunay3)=true);
  #
  FuncLift:=function()
    local ListCase, eExt, VO, EXT1, iD, EXT2, det12, iElt, EXTN, det1N, det2N, LV, eV, fV;
    ListCase:=[];
    for eExt in Concatenation(ListRelVertAdja, ListInfiniteDirection, ListDefinitionVertices, ListCVPvertices)
    do
      VO:=[eExt*TheDelaunay1.TheQuadFunction*eExt, eExt*TheDelaunay2.TheQuadFunction*eExt];
      if VO<>[0,0] then
        Add(ListCase, VO);
      fi;
    od;
    EXT1:=ListCase[1];
    iD:=1;
    while(true)
    do
      if iD=Length(ListCase) then
        return fail;
      fi;
      iD:=iD+1;
      EXT2:=ListCase[iD];
      det12:=EXT2[2]*EXT1[1]-EXT2[1]*EXT1[2];
      if (det12<>0) then
        break;
      fi;
    od;
    for iElt in [iD+1..Length(ListCase)]
    do
      EXTN:=ListCase[iElt];
      det1N:=EXTN[2]*EXT1[1]-EXTN[1]*EXT1[2];
      det2N:=EXTN[2]*EXT2[1]-EXTN[1]*EXT2[2];
      if (det1N*det2N>0) then
        if (det12*det1N>0) then
          EXT2:=ShallowCopy(EXTN);
          det12:=det1N;
        else
          EXT1:=ShallowCopy(EXTN);
          det12:=-det2N;
        fi;
      fi;
    od;
    if (det12>0) then
      LV:=[[-EXT1[2], EXT1[1]], [EXT2[2], -EXT2[1]]];
    else
      LV:=[[EXT1[2], -EXT1[1]], [-EXT2[2], EXT2[1]]];
    fi;
    for eV in LV
    do
      if eV[1]<>0 then
        fV:=RemoveFraction(eV);
        return RemoveFractionMatrix(fV[1]*TheDelaunay1.TheQuadFunction+fV[2]*TheDelaunay2.TheQuadFunction);
      fi;
    od;
  end;
  ListInfiniteDirection:=InfDel_GetEigenRationalConditions(TheDelaunay1.TheQuadForm, TheDelaunay2.TheQuadForm, TheDelaunay3.VectSpace);
  ListDefinitionVertices:=[];
  ListCVPvertices:=[];
  #
  sizExt:=1;
  Print("Entering lifting loop\n");
  while(true)
  do
    Print("passing in the while loop\n");
    while(true)
    do
      NewQuadFunction:=FuncLift();
      if NewQuadFunction<>fail then
        break;
      fi;
      Print("passing in the second while loop\n");
      Add(ListDefinitionVertices, InfDel_GetVertexRandomPoint(TheDelaunay3, sizExt));
      sizExt:=sizExt+1;
    od;
    NewQuadForm:=InfDel_GetQuadForm(NewQuadFunction);
    TheCVP:=InfDel_GetNegCVPVector(NewQuadFunction, TheDelaunay3);
    if TheCVP.TheResult=true then
      while(true)
      do
        if InfDel_IsFunctionNonNegative(NewQuadFunction)=true then
          break;
        fi;
        NewQuadFunction:=NewQuadFunction+TheDelaunay3.TheQuadFunction;
      od;
      NewQuadFunction:=NewQuadFunction+TheDelaunay3.TheQuadFunction;
      NewQuadForm:=InfDel_GetQuadForm(NewQuadFunction);
      TheNewEXT:=InfDel_GetZeroSet(NewQuadFunction);
      TheRec:=rec(n:=n, EXT:=TheNewEXT.EXT, VectSpace:=TheNewEXT.VectSpace, TheQuadFunction:=NewQuadFunction, TheQuadForm:=NewQuadForm);
      TheNewQuadFunction:=InfDel_GetCanonicalPosQuadFuncExpression(TheRec);
      TheNewQuadForm:=InfDel_GetQuadForm(TheNewQuadFunction);
      TheNewRec:=rec(n:=n, EXT:=TheNewEXT.EXT, VectSpace:=TheNewEXT.VectSpace, TheQuadFunction:=TheNewQuadFunction, TheQuadForm:=TheNewQuadForm);
      InfDel_CheckCoherencyDelaunay(TheRec);
      if InfDel_IsSubset(TheNewRec, TheDelaunay3)=false then
        Error("Lifting error case 1");
      fi;
      if Length(LinSpace2)<>Length(InfDel_GetLinearSpace(TheNewRec)) then
        Error("Lifting error case 2");
      fi;
      if InfDel_IsEqual(TheDelaunay1, InfDel_Intersection(TheDelaunay2, TheNewRec))=false then
        Error("Lifting error case 3");
      fi;
      return TheNewRec;
    fi;
    if TheCVP.TheResult=false then
      Append(ListCVPvertices, TheCVP.ListVect);
    fi;
    Print("|TheCVP.ListVect|=", Length(TheCVP.ListVect), "\n");
  od;
end;




#
#
# ---This method uses the generators to break the orbits.
#    It is known to fail in some cases, i.e. to give too few elements.
# Yet it is interesting in its own right, because:
# ---it is "almost" correct
# ---It is conceptually simple
# ---It gives lower bounds on the list of liftings.
InfDel_OrbitSplitting_BrokenLogical:=function(TheSuperDelaunay, TheDelaunay, ListOrbit)
  local TheBigGroupComplete, TheStabPair, testIsStab, TheBigGroup, NewListOrbit, eOrbit, PartialListOrbit, ListStatus, FuncInsert, nbClass, IsFinished, iClass, eGen, fOrbit;
  TheBigGroupComplete:=InfDel_CompleteStabilizer(TheDelaunay);
  TheStabPair:=InfDel_PairStabilizer(TheSuperDelaunay, TheDelaunay);
  testIsStab:=InfDel_IsStabilizer(TheSuperDelaunay, TheBigGroupComplete.GRPmatr);
  if testIsStab=true then
    return ListOrbit;
  fi;
  TheBigGroup:=InfDel_Stabilizer(TheDelaunay);
  NewListOrbit:=[];
  for eOrbit in ListOrbit
  do
    PartialListOrbit:=[];
    ListStatus:=[];
    FuncInsert:=function(eNewOrbit)
      local iClass, nbClass, test;
      nbClass:=Length(PartialListOrbit);
      for iClass in [1..nbClass]
      do
        test:=InfDel_TripleEquivalence(TheSuperDelaunay, TheDelaunay, PartialListOrbit[iClass], eNewOrbit);
        if test<>false then
          return;
        fi;
      od;
      Add(PartialListOrbit, eNewOrbit);
      Add(ListStatus, 0);
    end;
    FuncInsert(eOrbit);
    while(true)
    do
      nbClass:=Length(ListStatus);
      IsFinished:=true;
      for iClass in [1..nbClass]
      do
        if ListStatus[iClass]=0 then
          ListStatus[iClass]:=1;
          IsFinished:=false;
          eOrbit:=PartialListOrbit[iClass];
          for eGen in GeneratorsOfGroup(TheBigGroup.GRPmatr)
          do
            fOrbit:=InfDel_AffineTransformation(eOrbit, eGen);
            FuncInsert(fOrbit);
          od;
        fi;
      od;
      if IsFinished then
        break;
      fi;
    od;
    Append(NewListOrbit, PartialListOrbit);
  od;
  return NewListOrbit;
end;


InfDel_OrbitSplitting:=function(TheSuperDelaunay, TheDelaunay, ListOrbit)
  local TheBigGroupComplete, TheStabPair, testIsStab, TheBigGroup, ListRightCosets, LRCS, eRCS, ePerm, eMat, NewListOrbit, eOrbit, PartialListOrbit, FuncInsert, eBigMat, fOrbit, ListOrbitBrokenMethod;
  TheBigGroupComplete:=InfDel_CompleteStabilizer(TheDelaunay);
  TheStabPair:=InfDel_PairStabilizer(TheSuperDelaunay, TheDelaunay);
  testIsStab:=InfDel_IsStabilizer(TheSuperDelaunay, TheBigGroupComplete.GRPmatr);
  if testIsStab=true then
    return ListOrbit;
  fi;
  TheBigGroup:=InfDel_Stabilizer(TheDelaunay);
  Print("|TheBigGroup|=", Order(TheBigGroup.GRPperm), " |TheStabPair|=", Order(TheStabPair.GRPperm), "\n");
  ListRightCosets:=[];
  LRCS:=RightCosets(TheBigGroup.GRPperm, TheStabPair.GRPperm);
  for eRCS in LRCS
  do
    ePerm:=Representative(eRCS);
    eMat:=Image(TheBigGroup.phi, ePerm);
    Add(ListRightCosets, eMat);
  od;
  NewListOrbit:=[];
  for eOrbit in ListOrbit
  do
    PartialListOrbit:=[];
    FuncInsert:=function(eNewOrbit)
      local iClass, nbClass, test;
      nbClass:=Length(PartialListOrbit);
      for iClass in [1..nbClass]
      do
        test:=InfDel_TripleEquivalence(TheSuperDelaunay, TheDelaunay, PartialListOrbit[iClass], eNewOrbit);
        if test<>false then
          return;
        fi;
      od;
      Add(PartialListOrbit, eNewOrbit);
    end;
    for eBigMat in ListRightCosets
    do
      fOrbit:=InfDel_AffineTransformation(eOrbit, eBigMat);
      FuncInsert(fOrbit);
    od;
    Append(NewListOrbit, PartialListOrbit);
  od;
  ListOrbitBrokenMethod:=InfDel_OrbitSplitting_BrokenLogical(TheSuperDelaunay, TheDelaunay, ListOrbit);
  if Length(ListOrbitBrokenMethod)>Length(NewListOrbit) then
    Error("We clearly have a logical error");
  fi;
  return NewListOrbit;
end;





InfDel_OrbitSplitting_atp:=function(TheSuperDelaunay, TheDelaunay, ListOrbit)
  local n, NewListOrbit, eOrbit, PartialNewListOrbit, FuncInsert, IsFinished, nbOrbit, iOrbit, eRecDelaunay, eBigGen, eGen, TheImage, TheBigGroup, NewVectSpace, iOrbitMain, TheStab, testIsStab, ListStatus, ListMatrGens, TheBigGroupComplete, TheStabPair, TheSPC, p, TheBasis, AffBasis, InvAff, ListPermGens, NewEXTred, eEXTimg, New_eEXTimg, NewEXT, eList, TheInducedStab, FuncInsertOrbit, ListEXTrelevant, GetPositionListRelevant, eSet, GRPpermBig, GRPpermBigStab, GRPpermPair, eDCS, eMatr, eEXT, pos, phi, New_eEXTimgRed, VectSpaceExt, nbOrbitMain, LDCS, ListPermGensPair;
#  SaveDataToFile("ForDEBUG", rec(TheSuperDelaunay:=TheSuperDelaunay, TheDelaunay:=TheDelaunay, ListOrbit:=ListOrbit));
  Print("Begin InfDel_OrbitSplitting, |ListOrbit|=", Length(ListOrbit), "\n");
  n:=TheSuperDelaunay.n;
  NewListOrbit:=[];
  TheBigGroupComplete:=InfDel_CompleteStabilizer(TheDelaunay);
  TheStabPair:=InfDel_PairStabilizer(TheSuperDelaunay, TheDelaunay);
  testIsStab:=InfDel_IsStabilizer(TheSuperDelaunay, TheBigGroupComplete.GRPmatr);
  Print("|inner group|=", Order(TheBigGroupComplete.GRPperm), " |stab|=", Order(TheStabPair.GRPperm), " testIsStab=", testIsStab, "\n");
  if testIsStab=true then
    return ListOrbit;
  fi;
  TheBigGroup:=InfDel_Stabilizer(TheDelaunay);
  Print("We have TheBigGroup\n");
  TheSPC:=InfDel_BasisCompletion(TheDelaunay.VectSpace, IdentityMat(n), n);
  p:=Length(TheSPC);
  Print("|TheSuperDelaunay.VectSpace|=", Length(TheSuperDelaunay.VectSpace), "\n");
  Print("|TheDelaunay.VectSpace|=", Length(TheDelaunay.VectSpace), " p=", p, "\n");
  TheBasis:=Concatenation(TheSPC, TheDelaunay.VectSpace);
  AffBasis:=InfDel_GetAffineBasis(TheBasis);
  InvAff:=Inverse(AffBasis);
  NewEXT:=TheDelaunay.EXT*InvAff;
  NewEXTred:=List(NewEXT, x->x{[1..p+1]});
  ListPermGens:=[];
  for eGen in GeneratorsOfGroup(TheStabPair.TheMatrGRP)
  do
    eList:=[];
    for eEXT in TheDelaunay.EXT
    do
      eEXTimg:=eEXT*eGen;
      New_eEXTimg:=eEXTimg*InvAff;
      New_eEXTimgRed:=New_eEXTimg{[1..p+1]};
      pos:=Position(NewEXTred, New_eEXTimgRed);
      Add(eList, pos);
    od;
    Add(ListPermGens, PermList(eList));
  od;
  TheInducedStab:=Group(ListPermGens);
  #
  nbOrbitMain:=Length(ListOrbit);
  for iOrbitMain in [1..nbOrbitMain]
  do
    Print("iOrbitMain=", iOrbitMain, " / ", nbOrbitMain, "\n");
    eOrbit:=ListOrbit[iOrbitMain];
    VectSpaceExt:=List(eOrbit.VectSpace, x->Concatenation([0], x));
    ListEXTrelevant:=[];
    FuncInsertOrbit:=function(eEXT)
      local O, IsPresent, ListPoint, ListStatus, eGenComp, NewEXT, iPoint, FuncInsertPt;
      IsPresent:=function(eEXT)
        local fEXT;
        for fEXT in ListEXTrelevant
        do
          if Length(VectSpaceExt)=0 then
            if fEXT=eEXT then
              return true;
            fi;
          else
            if SolutionMat(VectSpaceExt, fEXT-eEXT)<>fail then
              return true;
            fi;
          fi;
        od;
        return false;
      end;
      ListPoint:=[];
      ListStatus:=[];
      FuncInsertPt:=function(eEXT)
        if IsPresent(eEXT) then
          return;
        fi;
        Add(ListEXTrelevant, eEXT);
        Add(ListPoint, eEXT);
        Add(ListStatus, 1);
      end;
      FuncInsertPt(eEXT);
      while(true)
      do
        IsFinished:=true;
        for iPoint in [1..Length(ListPoint)]
        do
          if ListStatus[iPoint]=1 then
            ListStatus[iPoint]:=0;
            IsFinished:=false;
            for eGenComp in GeneratorsOfGroup(TheBigGroupComplete.GRPmatr)
            do
              NewEXT:=ListPoint[iPoint]*eGenComp;
              FuncInsertPt(NewEXT);
            od;
          fi;
        od;
        if IsFinished then
          break;
        fi;
      od;
    end;
    for eEXT in eOrbit.EXT
    do
      FuncInsertOrbit(eEXT);
    od;
    Print("All points have been inserted\n");
    GetPositionListRelevant:=function(eEXT)
      local iEXT;
      for iEXT in [1..Length(ListEXTrelevant)]
      do
        if Length(VectSpaceExt)=0 then
          if ListEXTrelevant[iEXT]=eEXT then
            return iEXT;
          fi;
        else
          if SolutionMat(VectSpaceExt, ListEXTrelevant[iEXT]-eEXT)<>fail then
            return iEXT;
          fi;
        fi;
      od;
      Error("We should never reach that stage");
    end;
    ListPermGens:=[];
    ListMatrGens:=GeneratorsOfGroup(TheBigGroupComplete.GRPmatr);
    for eGen in ListMatrGens
    do
      eList:=List(ListEXTrelevant, x->GetPositionListRelevant(x*eGen));
      Add(ListPermGens, PermList(eList));
    od;
    Print("ListPermGens computed\n");
    GRPpermBig:=Group(ListPermGens);
    phi:=GroupHomomorphismByImagesNC(GRPpermBig, TheBigGroupComplete.GRPmatr, ListPermGens, ListMatrGens);
    Print("phi computed\n");
    ListPermGensPair:=[];
    for eGen in GeneratorsOfGroup(TheStabPair.TheMatrGRP)
    do
      eList:=List(ListEXTrelevant, x->GetPositionListRelevant(x*eGen));
      Add(ListPermGensPair, PermList(eList));
    od;
    Print("ListPermGensPair computed\n");
    GRPpermPair:=Group(ListPermGensPair);
    eSet:=Set(List(eOrbit.EXT, GetPositionListRelevant));
    Print("eSet computed\n");
    GRPpermBigStab:=Stabilizer(GRPpermBig, eSet, OnSets);
    PartialNewListOrbit:=[];
    LDCS:=DoubleCosets(GRPpermBig, GRPpermBigStab, GRPpermPair);
    Print("LDCS computed\n");
    for eDCS in LDCS
    do
      eMatr:=Image(phi, Representative(eDCS));
      TheImage:=InfDel_AffineTransformation(eOrbit, eMatr);
      Add(PartialNewListOrbit, TheImage);
    od;
    Append(NewListOrbit, PartialNewListOrbit);
  od;
  Print("End InfDel_OrbitSplitting, |NewListOrbit|=", Length(NewListOrbit), "\n");
  return NewListOrbit;
end;



InfDel_GetRecord:=function(EXT, eOrbit, TheSuperQuadFunction)
  local n, TheRec, LinSpa, TheDiff, ListCorrect, eQuadFunction, nbP, nbM, nbZ, eEXT, eVal, TheNewQuadForm, hVect, cCent, rSquare, TheCVP, TheCVPext, TheNewQuadFunction;
  n:=Length(TheSuperQuadFunction)-1;
  TheRec:=rec(n:=n, EXT:=EXT{eOrbit}, VectSpace:=[]);
  LinSpa:=InfDel_GetLinearSpace(TheRec);
  TheDiff:=EXT{Difference([1..Length(EXT)], eOrbit)};
  ListCorrect:=[];
  for eQuadFunction in LinSpa
  do
    nbP:=0;
    nbM:=0;
    nbZ:=0;
    for eEXT in TheDiff
    do
      eVal:=eEXT*eQuadFunction*eEXT;
      if eVal < 0 then
        nbM:=nbM+1;
      else
        if eVal > 0 then
          nbP:=nbP+1;
        else
          nbZ:=nbZ+1;
        fi;
      fi;
    od;
    if nbM>0 and nbP>0 then
      Error("Not correct, something wrong 1");
    fi;
    if nbM>0 and nbZ>0 then
      Error("Not correct, something wrong 2");
    fi;
    if nbP>0 and nbZ>0 then
      Error("Not correct, something wrong 3");
    fi;
    if nbP>0 then
      Add(ListCorrect, eQuadFunction);
    else
      if nbM>0 then
        Add(ListCorrect, -eQuadFunction);
      fi;
    fi;
  od;
  if Length(ListCorrect)=0 then
    Error("Incorrect, bis 1");
  fi;
  #
  TheNewQuadFunction:=ListCorrect[1];
  while(true)
  do
    TheNewQuadForm:=InfDel_GetQuadForm(TheNewQuadFunction);
    if IsPositiveDefiniteSymmetricMatrix(TheNewQuadForm)=true then
      break;
    fi;
    TheNewQuadFunction:=TheNewQuadFunction+TheSuperQuadFunction;
  od;
  while(true)
  do
    TheNewQuadForm:=InfDel_GetQuadForm(TheNewQuadFunction);
    hVect:=TheNewQuadFunction[1]{[2..n+1]};
    cCent:=-hVect*Inverse(TheNewQuadForm);
    rSquare:=cCent*TheNewQuadForm*cCent-TheNewQuadFunction[1][1];
    TheCVP:=CVPVallentinProgram(TheNewQuadForm, cCent);
    TheCVPext:=List(TheCVP.ListVect, x->Concatenation([1], x));
    if TheCVP.TheNorm=rSquare and Set(TheCVPext)=Set(EXT{eOrbit}) then
      break;
    fi;
    TheNewQuadFunction:=TheNewQuadFunction+TheSuperQuadFunction;
  od;
  TheRec.TheQuadFunction:=TheNewQuadFunction;
  TheRec.TheQuadForm:=TheNewQuadForm;
  InfDel_CheckCoherencyDelaunay(TheRec);
  return TheRec;
end;

InfDel_MyDualDescriptionStandard:=function(EXT, PermGRP, BFpoly)
  local IsRespawn, IsBankSave, nbExt, WorkingDim, TmpDir, DataPolyhedral, MyDualDescription;
  nbExt:=Length(EXT);
  #
  #
  IsRespawn:=function(OrdGRP, EXT, TheDepth)
    local rnk;
    rnk:=RankMat(EXT);
    Print("OrdGRP=", OrdGRP, " TheDepth=", TheDepth, " |EXT|=", Length(EXT), " rnk=", rnk, "\n");
    if OrdGRP>=100 and TheDepth<=2 and Length(EXT) > 10 + rnk then
      return true;
    fi;
    if OrdGRP>=96 and TheDepth=3 and Length(EXT)>=48 and rnk=26 then
      return true;
    fi;
    if OrdGRP<100 then
      return false;
    fi;
    if Length(EXT) < rnk+7 then
      return false;
    fi;
    if OrdGRP>1000 and Length(EXT) > rnk + 15 then
      return true;
    fi;
    if TheDepth>=3 then
      return false;
    fi;
    return true;
  end;
  IsBankSave:=function(EllapsedTime, OrdGRP, EXT, TheDepth)
    if TheDepth=0 then
      return false;
    fi;
    if EllapsedTime>=600 then
      return true;
    fi;
    return true;
  end;
  TmpDir:=Filename(POLYHEDRAL_tmpdir, "");
  MyDualDescription:=function(EXT, GroupExt, ThePath)
    if Length(EXT) > 1000 then
      return __DualDescriptionCDD_Reduction(EXT, GroupExt, ThePath);
    fi;
    return __DualDescriptionLRS_Reduction(EXT, GroupExt, ThePath);
  end;
  DataPolyhedral:=rec(IsBankSave:=IsBankSave, 
        TheDepth:=0,
        IsRespawn:=IsRespawn, 
        GetInitialRays:=GetInitialRays_LinProg,
        ProjectionLiftingFramework:=__ProjectionLiftingFramework,
        Saving:=false,
        ThePathSave:="/irrelevant/",
        ThePath:=TmpDir,
        DualDescriptionFunction:=MyDualDescription, 
        GroupFormalism:=OnSetsGroupFormalism(500));
  return __ListFacetByAdjacencyDecompositionMethod(EXT, PermGRP, DataPolyhedral, BFpoly);
end;

InfDel_GetMatrixInvariant:=function(TheMat)
  local TheDiag, TheOffDiag, iVert, nbVert;
  nbVert:=Length(TheMat);
  TheDiag:=List([1..nbVert], x->TheMat[x][x]);
  TheOffDiag:=[];
  for iVert in [1..nbVert-1]
  do
    Append(TheOffDiag, TheMat{[iVert+1..nbVert]});
  od;
  return rec(CollDiag:=Collected(TheDiag), CollOffDiag:=Collected(TheOffDiag));
end;

InfDel_GetInvariant:=function(eDelaunay)
  local len, n, TheCompl, NewBasis, AffBasis, p, NewEXT, eEXT, hEXT, eNewEXT, DDA, TheDegSkel, ListDegSkel, TheDegDualSkel, ListDegDualSkel, DoAdjInvariant, DoMetricInvariant, TheGram, AdjInv, MetricInv, nbVert;
  len:=Length(eDelaunay.VectSpace);
  nbVert:=Length(eDelaunay.EXT);
  n:=eDelaunay.n;
  TheCompl:=InfDel_BasisCompletion(eDelaunay.VectSpace, IdentityMat(n), n);
  NewBasis:=Concatenation(TheCompl, eDelaunay.VectSpace);
  AffBasis:=InfDel_GetAffineBasis(NewBasis);
  p:=Length(TheCompl);
  NewEXT:=[];
  for eEXT in eDelaunay.EXT
  do
    hEXT:=eEXT*Inverse(AffBasis);
    eNewEXT:=hEXT{[1..p+1]};
    Add(NewEXT, eNewEXT);
  od;
  DoAdjInvariant:=false;
  if DoAdjInvariant=true then
    DDA:=DualDescriptionAdjacencies(NewEXT);
    TheDegSkel:=DDA.SkeletonGraph.order;
    ListDegSkel:=List([1..TheDegSkel], x->Length(Adjacency(DDA.SkeletonGraph, x)));
    TheDegDualSkel:=DDA.RidgeGraph.order;
    ListDegDualSkel:=List([1..TheDegDualSkel], x->Length(Adjacency(DDA.RidgeGraph, x)));
    AdjInv:=rec(CollSkel:=Collected(ListDegSkel), CollDualSkel:=Collected(ListDegDualSkel));
  else
    AdjInv:=0;
  fi;
  DoMetricInvariant:=false;
  if DoMetricInvariant=true then
    TheGram:=InfDel_GetGramDiscMat(eDelaunay, eDelaunay.EXT);
    MetricInv:=InfDel_GetMatrixInvariant(TheGram);
  else
    MetricInv:=0;
  fi;
  return rec(AdjInv:=AdjInv, MetricInv:=MetricInv, len:=len, nbVert:=nbVert);
end;

InfDel_GetInvariantPair:=function(TheSuperPolytope, ThePolytope)
  local ListDistMat, TheDistMat, TheInv1, TheInv2;
  ListDistMat:=[];
  Add(ListDistMat, InfDel_GetGramDiscMat(ThePolytope, ThePolytope.EXT));
  Add(ListDistMat, InfDel_GetGramDiscMat(TheSuperPolytope, ThePolytope.EXT));
  TheDistMat:=InfDel_MergeDistMatrices(ListDistMat);
  TheInv1:=InfDel_GetInvariant(ThePolytope);
  TheInv2:=InfDel_GetMatrixInvariant(TheDistMat);
  return rec(TheInv1:=TheInv1, TheInv2:=TheInv2);
end;




InfDel_GetValueVector:=function(eVect)
  return SymmetricMatrixToVector(TransposedMat([eVect])*[eVect]);
end;

InfDel_SubDelaunayPolytopes:=function(Data, TheDelaunay)
  local n, GRPinner, TheVect, TheDim, SubEXT, eEXT, VectSpace, nVect, LamQuadForm, OneVert, val1, val2, LamQuadFunction, i, j, TheBeginSub, ListOrbit, FuncInsert, perfrnk, rnk, DimSpace, nbOrbit, SelectedSpaceRank, SelectedNumberVertices, iOrbitSelect, IsUndoneInfinity, TotalNrLateralCases, eDimSpace, nbVert, TheNb, iOrbit, TheLiftDelaunay, eOrbitSub, ListOrbitSubs, ListOrbitSubsSplitted, TheRec, ListIncidentValues, ListOrbHinge, eOrbit, iOrbitSub, testBank, TheNewForm, TheNewFunction, TheDimBis, ListNbOrbitByRank, ListNbOrbitByRankUndone, ListInvariant, nbOrbitSub, ListStatus;
  InfDel_CheckCoherencyDelaunay(TheDelaunay);
  n:=TheDelaunay.n;
  GRPinner:=InfDel_Stabilizer(TheDelaunay);
  testBank:=Data.FuncRetrieveListOrbit(TheDelaunay);
  if testBank<>false then
    return testBank;
  fi;
  Print("|GRPinner.GRPperm|=", Order(GRPinner.GRPperm), "\n");
  if Length(TheDelaunay.VectSpace)=0 then
    ListIncidentValues:=List(TheDelaunay.EXT, InfDel_GetValueVector);
    Print("Calling DualDescriptionStandard with\n");
    Print("|ListIncidentValues|=", Length(ListIncidentValues), " |GRPperm|=", Order(GRPinner.GRPperm), "\n");
    ListOrbHinge:=InfDel_MyDualDescriptionStandard(ListIncidentValues, GRPinner.GRPperm, Data.BFpoly);
    ListOrbit:=[];
    for eOrbit in ListOrbHinge
    do
      TheRec:=InfDel_GetRecord(TheDelaunay.EXT, eOrbit, TheDelaunay.TheQuadFunction);
      Add(ListOrbit, TheRec);
    od;
    return ListOrbit;
  fi;
  TheVect:=TheDelaunay.VectSpace[1];
  TheDim:=Length(TheDelaunay.VectSpace);
  SubEXT:=[];
  for eEXT in TheDelaunay.EXT
  do
    Add(SubEXT, eEXT);
    Add(SubEXT, eEXT+Concatenation([0], TheVect));
  od;
  VectSpace:=Concatenation(TheDelaunay.VectSpace{[2..TheDim]}, List(TheDelaunay.EXT, x->x{[2..n+1]}-TheDelaunay.EXT[1]{[2..n+1]}));
  nVect:=NullspaceIntMat(TransposedMat(VectSpace))[1];
  LamQuadForm:=TransposedMat([nVect])*[nVect];
  OneVert:=TheDelaunay.EXT[1];
  val1:=OneVert{[2..n+1]}*nVect;
  val2:=val1+TheVect*nVect;
  TheBeginSub:=rec(n:=n, EXT:=SubEXT, VectSpace:=TheDelaunay.VectSpace{[2..TheDim]});
  LamQuadFunction:=InfDel_Get012form(TheBeginSub, LamQuadForm);
  TheNewFunction:=RemoveFractionMatrix(TheDelaunay.TheQuadFunction+LamQuadFunction);
  TheNewForm:=InfDel_GetQuadForm(TheNewFunction);
  TheBeginSub.TheQuadForm:=TheNewForm;
  TheBeginSub.TheQuadFunction:=TheNewFunction;
  InfDel_CheckCoherencyDelaunay(TheBeginSub);
  ListOrbit:=[];
  ListInvariant:=[];
  ListStatus:=[];
  FuncInsert:=function(eDelaunay)
    local iRecord, eRecord, TheNewRecord, TheStab, test, ListAdjacentVert, eInv;
    if InfDel_IsSubset(eDelaunay, TheDelaunay)=false then
      Error("Lifting: Failure of inclusion property 1");
    fi;
    eInv:=InfDel_GetInvariant(eDelaunay);
    for iRecord in [1..Length(ListOrbit)]
    do
      if ListInvariant[iRecord]=eInv then
        eRecord:=ListOrbit[iRecord];
        test:=InfDel_PairEquivalence(TheDelaunay, eRecord, eDelaunay);
        if test<>false then
          return;
        fi;
      fi;
    od;
    TheStab:=InfDel_PairStabilizer(TheDelaunay, eDelaunay);
    ListAdjacentVert:=InfDel_GetAdjacentVertices(eDelaunay); 
    TheNewRecord:=rec(n:=n, EXT:=eDelaunay.EXT, VectSpace:=eDelaunay.VectSpace, TheQuadForm:=eDelaunay.TheQuadForm, TheQuadFunction:=eDelaunay.TheQuadFunction, TheStab:=TheStab, ListAdjacentVert:=ListAdjacentVert);
    Add(ListOrbit, TheNewRecord);
    Add(ListInvariant, eInv);
    Add(ListStatus, "NO");
    Print("Now, the number of Delaunay polytopes is ", Length(ListInvariant), "\n");
  end;
  FuncInsert(TheBeginSub);
  perfrnk:=Length(InfDel_GetLinearSpace(TheDelaunay));
  rnk:=RankMat(TheDelaunay.EXT);
  TheDimBis:=Length(TheDelaunay.VectSpace[1]);
  DimSpace:=(TheDimBis+1)*(TheDimBis+2)/2-perfrnk-2;
  while(true)
  do
    nbOrbit:=Length(ListOrbit);
    SelectedSpaceRank:=n*n+n+30;     # over possible values
    SelectedNumberVertices:=2^(n+2); # over possible values
    iOrbitSelect:=-1;
    IsUndoneInfinity:=false;
    TotalNrLateralCases:=0;
    ListNbOrbitByRank:=ListWithIdenticalEntries(n,0);
    ListNbOrbitByRankUndone:=ListWithIdenticalEntries(n,0);
    for iOrbit in [1..nbOrbit]
    do
      eDimSpace:=Length(ListOrbit[iOrbit].VectSpace);
      ListNbOrbitByRank[eDimSpace+1]:=ListNbOrbitByRank[eDimSpace+1]+1;
      if ListStatus[iOrbit]="NO" then
        ListNbOrbitByRankUndone[eDimSpace+1]:=ListNbOrbitByRankUndone[eDimSpace+1]+1;
        nbVert:=Length(ListOrbit[iOrbit].EXT);
        if eDimSpace<SelectedSpaceRank then
          iOrbitSelect:=iOrbit;
          SelectedSpaceRank:=eDimSpace;
          SelectedNumberVertices:=nbVert;
        else
          if eDimSpace=SelectedSpaceRank and nbVert<SelectedNumberVertices then
            iOrbitSelect:=iOrbit;
            SelectedNumberVertices:=nbVert;
          fi;
        fi;
        if eDimSpace<Length(TheDelaunay.VectSpace) then
          IsUndoneInfinity:=true;
        else
          TheNb:=Order(GRPinner.GRPperm)/Order(ListOrbit[iOrbit].TheStab.GRPperm);
          TotalNrLateralCases:=TotalNrLateralCases+TheNb;
        fi;
      fi;
    od;
    Print("TotalNrLateralCases=", TotalNrLateralCases, " DimSpace=", DimSpace, " rnk=", rnk, " perfrnk=", perfrnk, " \n");
    Print("  NbOrbit=", ListNbOrbitByRank, "  Undone=", ListNbOrbitByRankUndone, "\n");
    if IsUndoneInfinity=true then
      ListStatus[iOrbitSelect]:="YES";
      ListOrbitSubs:=InfDel_SubDelaunayPolytopes(Data, ListOrbit[iOrbitSelect]);
      ListOrbitSubsSplitted:=InfDel_OrbitSplitting(TheDelaunay, ListOrbit[iOrbitSelect], ListOrbitSubs);
      nbOrbitSub:=Length(ListOrbitSubsSplitted);
      for iOrbitSub in [1..nbOrbitSub]
      do
        eOrbitSub:=ListOrbitSubsSplitted[iOrbitSub];
        Print("iOrbitSub=", iOrbitSub, "/", nbOrbitSub, "\n");
        TheLiftDelaunay:=InfDel_LiftingDelaunay(eOrbitSub, ListOrbit[iOrbitSelect], TheDelaunay);
        InfDel_CheckCoherencyDelaunay(TheLiftDelaunay);
        FuncInsert(TheLiftDelaunay);
      od;
    else
      break;
    fi;
  od;
  if Data.IsBankSave(TheDelaunay)=true then
    Data.FuncCreateAccount(TheDelaunay, ListOrbit);
  fi;
  return ListOrbit;
end;

InfDel_BankingFormalism:=function(ThePath)
  local ListOrbitDelaunay, FuncRetrieveListOrbit, FuncCreateAccount, FuncGetAllInfo, FileSave, FileSaveDesc, iFile;
  ListOrbitDelaunay:=[];
  iFile:=0;
  while(true)
  do
    FileSave:=Concatenation(ThePath, "EXT", String(iFile+1));
    FileSaveDesc:=Concatenation(ThePath, "EXTdesc", String(iFile+1));
#    Print("FileSave=", FileSave, "\n");
#    Print("FileSaveDesc=", FileSaveDesc, "\n"); 
    if IsExistingFilePlusTouch(FileSave)=false or IsExistingFilePlusTouch(FileSaveDesc)=false then
      break;
    fi;
    iFile:=iFile+1;
    Add(ListOrbitDelaunay, ReadAsFunction(FileSave)());
  od;
  Print("Database size : |ListOfbitDelaunay|=", Length(ListOrbitDelaunay), "\n");
  FuncRetrieveListOrbit:=function(TheDelaunay)
    local iOrbit, test, testInv, eOrbit, eNewOrbit, NewListOrbit, FileSaveDesc;
    for iOrbit in [1..Length(ListOrbitDelaunay)]
    do
      test:=InfDel_TestEquivalence(ListOrbitDelaunay[iOrbit], TheDelaunay);
      if test<>false then
        testInv:=Inverse(test);
        NewListOrbit:=[];
        FileSaveDesc:=Concatenation(ThePath, "EXTdesc", String(iOrbit));
        for eOrbit in ReadAsFunction(FileSaveDesc)()
        do
          eNewOrbit:=InfDel_AffineTransformation(eOrbit, testInv);
          if InfDel_IsSubset(eNewOrbit, TheDelaunay)=false then
            Error("Bank error, not in your favor");
          fi;
          Add(NewListOrbit, eNewOrbit);
        od;
        return NewListOrbit;
      fi;
    od;
    return false;
  end;
  FuncCreateAccount:=function(TheDelaunay, TheSubDelaunay)
    local nbOrbit, FileSaveDesc;
    Add(ListOrbitDelaunay, TheDelaunay);
    nbOrbit:=Length(ListOrbitDelaunay);
    FileSave:=Concatenation(ThePath, "EXT", String(nbOrbit));
    SaveDataToFilePlusTouch(FileSave, TheDelaunay);
    FileSaveDesc:=Concatenation(ThePath, "EXTdesc", String(nbOrbit));
    SaveDataToFilePlusTouch(FileSaveDesc, TheSubDelaunay);
  end;
  return rec(FuncCreateAccount:=FuncCreateAccount, FuncRetrieveListOrbit:=FuncRetrieveListOrbit);
end;





InfDel_SubDelaunayPolytopesKernel:=function(TheDelaunay, ThePath, ThePathPoly)
  local ZeroDelaunay, IsBankSave, Data, BF, BFpoly, FuncStabilizer, FuncIsomorphy, FuncInvariant;
  IsBankSave:=function(TheDelaunay)
    return true;
  end;
  BF:=InfDel_BankingFormalism(ThePath);
  FuncStabilizer:=function(EXTask)
    return LinPolytope_Automorphism(EXTask);
  end;
  FuncIsomorphy:=function(EXT1, EXT2)
    local TheEquiv;
    TheEquiv:=LinPolytope_Isomorphism(EXT1, EXT2);
    if TheEquiv=false then
      return false;
    else
      return PermList(TheEquiv);
    fi;
  end;
  FuncInvariant:=function(EXT)
    return [Length(EXT), RankMat(EXT)];
  end;
  BFpoly:=BankRecording(rec(Saving:=true, BankPath:=ThePathPoly), FuncStabilizer, FuncIsomorphy, FuncInvariant, OnSetsGroupFormalism(500));
  Data:=rec(IsBankSave:=IsBankSave, 
          FuncCreateAccount:=BF.FuncCreateAccount, 
          FuncRetrieveListOrbit:=BF.FuncRetrieveListOrbit, 
          BFpoly:=BFpoly);
  return InfDel_SubDelaunayPolytopes(Data, TheDelaunay);
end;

InfDel_SubDelaunayPolytopesGeneric:=function(TheDelaunay)
  local ThePath, ThePathPoly;
  ThePath:=Filename(POLYHEDRAL_tmpdir, "BankInfDel/");
  ThePathPoly:=Filename(POLYHEDRAL_tmpdir, "BankPoly/");
  Exec("mkdir -p ", ThePath);
  Exec("mkdir -p ", ThePathPoly);
  return InfDel_SubDelaunayPolytopesKernel(TheDelaunay, ThePath, ThePathPoly);
end;

InfDel_ClassificationDimensionN:=function(n)
  local ThePath, ThePathPoly, ZeroDelaunay;
  ThePath:=Concatenation("./BankInfDel_", String(n), "/");
  Exec("mkdir -p ", ThePath);
  ThePathPoly:=Concatenation("./BankPoly_", String(n), "/");
  Exec("mkdir -p ", ThePathPoly);
  ZeroDelaunay:=InfDel_ZerForm(n);
  return InfDel_SubDelaunayPolytopesKernel(ZeroDelaunay, ThePath, ThePathPoly);
end;


GetInhomogeneousForm:=function(EXT, TheQuadForm)
  local n, ListEqua, ListB, eVert, eVertRed, eLine, eNorm, eSol, TheQuadFunc, i, j, test, EXTsel;
  EXTsel:=RowReduction(EXT).EXT;
  n:=Length(EXT[1])-1;
  ListEqua:=[];
  ListB:=[];
  for eVert in EXTsel
  do
    eVertRed:=eVert{[2..n+1]};
    eLine:=Concatenation([1], 2*eVertRed);
    Add(ListEqua, eLine);
    eNorm:=eVertRed*TheQuadForm*eVertRed;
    Add(ListB, -eNorm);
  od;
  eSol:=ListB*Inverse(TransposedMat(ListEqua));
  TheQuadFunc:=NullMat(n+1,n+1);
  for i in [1..n]
  do
    for j in [1..n]
    do
      TheQuadFunc[i+1][j+1]:=TheQuadForm[i][j];
    od;
  od;
  for i in [1..n]
  do
    TheQuadFunc[1][i+1]:=eSol[i+1];
    TheQuadFunc[i+1][1]:=eSol[i+1];
  od;
  TheQuadFunc[1][1]:=eSol[1];
  test:=First(EXT, x->x*TheQuadFunc*x<>0);
  if test<>fail then
    Error("Matrix error, please debug");
  fi;
  return TheQuadFunc;
end;

ExtendByTriangleIneq:=function(EXTinput)
  local ListVert, len, eSet, eSum, j, eVertN;
  ListVert:=[];
  len:=Length(EXTinput);
  for eSet in Combinations([1..len],2)
  do
    eSum:=EXTinput[eSet[1]] + EXTinput[eSet[2]];
    for j in Difference([1..len], eSet)
    do
      eVertN:=eSum - EXTinput[j];
      Add(ListVert, eVertN);
    od;
  od;
  return Union(Set(ListVert), Set(EXTinput));
end;


RandomFindNegativeVector:=function(EXTinput, QuadFunc)
  local EXTwork, test, ListNeg;
  EXTwork:=EXTinput;
  while(true)
  do
    EXTwork:=ExtendByTriangleIneq(EXTwork);
    Print("|EXTwork|=", Length(EXTwork), "\n");
    ListNeg:=Filtered(EXTwork, x->x*QuadFunc*x<0);
    if Length(ListNeg)>0 then
      Print("|ListNeg|=", Length(ListNeg), "\n");
      return ListNeg;
    fi;
  od;
end;

GetInvariantSymmetricMatrixBasis:=function(EXT)
  local n, GRP, ListGen, eMatrGen, eMat, TheBasis, ListEqua, ListEquaRed, NSPvector, RetBasis, eNSP, TheMat, i, eGen;
  n:=Length(EXT[1])-1;
  GRP:=LinPolytopeIntegral_Automorphism(EXT);
  ListGen:=List(GeneratorsOfGroup(GRP.GRPmatr), x->FuncExplodeBigMatrix(x).MatrixTransformation);
  TheBasis:=InvariantFormDutourVersion(ListGen);
  #
  ListEqua:=ListEqualitiesDelaunay(EXT, TheBasis);
  ListEquaRed:=List(ListEqua, x->x{[2..Length(TheBasis)+1]});
  NSPvector:=NullspaceMat(TransposedMat(ListEquaRed));
  RetBasis:=[];
  for eNSP in NSPvector
  do
    TheMat:=NullMat(n,n);
    for i in [1..Length(TheBasis)]
    do
      TheMat:=TheMat + eNSP[i]*TheBasis[i];
    od;
    Add(RetBasis, TheMat);
  od;
  return RetBasis;
end;


GetAllNegativePoints:=function(TheFunc)
  local n, QuadForm, hVect, cCent, rSquare;
  n:=Length(TheFunc)-1;
  QuadForm:=List(TheFunc{[2..n+1]}, x->x{[2..n+1]});
  if IsPositiveDefiniteSymmetricMatrix(QuadForm)=false then
    Error("The matrx should be positive definite");
  fi;
  hVect:=TheFunc[1]{[2..n+1]};
  cCent:= - hVect*Inverse(QuadForm);
  rSquare:=cCent*QuadForm*cCent - TheFunc[1][1];
  return ClosestAtDistanceVallentinProgram(QuadForm, cCent, rSquare);
end;


GetAllNegativePoints:=function(TheFunc, UpperLimit)
  local n, QuadForm, hVect, cCent, rSquare, recOption;
  n:=Length(TheFunc)-1;
  QuadForm:=List(TheFunc{[2..n+1]}, x->x{[2..n+1]});
  if IsPositiveDefiniteSymmetricMatrix(QuadForm)=false then
    Error("The matrx should be positive definite");
  fi;
  hVect:=TheFunc[1]{[2..n+1]};
  cCent:= - hVect*Inverse(QuadForm);
  rSquare:=cCent*QuadForm*cCent - TheFunc[1][1];
  recOption:=rec(MaxVector:=UpperLimit, UseExactArithmetic:=true);
  return General_ClosestAtDistanceVallentinProgram(QuadForm, cCent, rSquare, recOption);
end;


GetLowestPoints:=function(TheFunc)
  local n, QuadForm, hVect, cCent, rSquare;
  n:=Length(TheFunc)-1;
  QuadForm:=List(TheFunc{[2..n+1]}, x->x{[2..n+1]});
  hVect:=TheFunc[1]{[2..n+1]};
  cCent:= - hVect*Inverse(QuadForm);
  rSquare:=cCent*QuadForm*cCent - TheFunc[1][1];
  return CVPVallentinProgram_Rational(QuadForm, cCent).ListVect;
end;





Vect_L1norm:=function(x)
  return Sum(List(x, AbsInt));
end;


TestRealizabilityDelaunay_Space:=function(EXT, TheBasis)
  local n, ListQuadFunc, pLin, EXTinput, TheDelaunay, ListIneq, ToBeMinimized, TheLP, eVert, eVect, eEnt, TheFunc, TheCVP, TheReply, sizExt, eIneq, eVertRand, i, TheFuncInt, eVertN, CritVal, ListVect, FuncExtendByListVect, ListNew, sizAllow, TheQuadForm, NewVect, eLimitEXT, MaxNorm, DoGeom, OptChoice, ListVert, ListNorm, MinNorm, posVert, UpperLimit, QuadForm, eNSP, IsDone, eRecMin, DoHeuristic, ExtensionByMovingFacet, eTr, DoReduction, IdxSel, NewVert, ListDeny, eOptimal, TheDiff, iter;
  n:=Length(EXT[1])-1;
  ListQuadFunc:=List(TheBasis, x->GetInhomogeneousForm(EXT, x));
  pLin:=Length(ListQuadFunc);
  ToBeMinimized:=ListWithIdenticalEntries(pLin+1,0);
  for i in [1..pLin]
  do
    eTr:=Trace(TheBasis[i]);
    ToBeMinimized[1+i]:=eTr;
  od;
  ListVect:=IdentityMat(n);
  FuncExtendByListVect:=function(EXTinput)
    local EXTret, eVect, eVectB, eEXT;
    EXTret:=[];
    for eEXT in Concatenation(Set(EXTinput), Set(EXT))
    do
      for eVect in ListVect
      do
        eVectB:=Concatenation([0], eVect);
        Add(EXTret, eEXT + eVectB);
      od;
    od;
    return Difference(Set(EXTret), Set(EXT));
  end;
  ExtensionByMovingFacet:=function(shift)
    local FAC, FACint, FACext, eFAC, nFAC, TheResult, EXTret, NewEXT, eEXT;
    FAC:=DualDescription(EXT);
    FACint:=List(FAC, RemoveFraction);
    FACext:=[];
    for eFAC in FACint
    do
      nFAC:=Concatenation([eFAC[1]+shift], eFAC{[2..n+1]});
      Add(FACext, nFAC);
    od;
    TheResult:=RunZsolve(FACext);
    EXTret:=[];
    for eEXT in TheResult.TheINH
    do
      NewEXT:=Concatenation([1],eEXT);
      if Position(EXT, NewEXT)=fail then
        Add(EXTret, NewEXT);
      fi;
    od;
    return EXTret;
  end;

  EXTinput:=FuncExtendByListVect([]);
#  EXTinput:=ExtensionByMovingFacet(2);
  TheDelaunay:=rec(n:=n,
                   EXT:=EXT,
                   VectSpace:=[]);
  for NewVect in IdentityMat(n)
  do
    NewVert:=Concatenation([0], NewVect);
    Add(EXTinput, NewVert);
  od;
  iter:=0;
  while(true)
  do
    iter:=iter+1;
    Print("iter=", iter, "\n");
    ListDeny:=[];
    ListIneq:=[];
    for eVert in EXTinput
    do
      eIneq:=Concatenation([-1], List(ListQuadFunc, x->eVert*x*eVert));
      Add(ListIneq, eIneq);
    od;
    Print("  |ListIneq|=", Length(ListIneq), "\n");
#    if Length(ListIneq)=200 then
#      Print("Try your luck at this point\n");
#      Print(NullMat(5));
#    fi;
    TheLP:=LinearProgramming(ListIneq, ToBeMinimized);
    if IsBound(TheLP.primal_direction) then
      Error("A priori, the trace should be well defined and at least non-negative");
    fi;
    if IsBound(TheLP.optimal) then
      eOptimal:=TheLP.optimal;
      Print("  LP solved optimal=", TheLP.optimal, "\n");
    else
      Print("  LP solved\n");
    fi;
    if IsBound(TheLP.primal_solution)=false then
      Print("End of TestRealizabilityDelaunay_Space\n");
      return rec(reply:=false, TheLP:=TheLP, EXTinput:=EXTinput, ListQuadFunc:=ListQuadFunc);
    fi;
    eVect:=ListWithIdenticalEntries(pLin, 0);
    for eEnt in TheLP.primal_solution
    do
      eVect[eEnt[1]]:=eEnt[2];
    od;
    TheFunc:=NullMat(n+1,n+1);
    for i in [1..pLin]
    do
      TheFunc:=TheFunc+eVect[i]*ListQuadFunc[i];
    od;
    if First(EXTinput, x->x*TheFunc*x<1)<>fail then
      Error("Inconsistency in TheFunc");
    fi;
    TheFuncInt:=RemoveFractionMatrix(TheFunc);
    TheQuadForm:=List(TheFuncInt{[2..n+1]}, x->x{[2..n+1]});
    CritVal:=100000;
    DoGeom:=false;
    if InfDel_L1Norm(TheFuncInt) > CritVal and DoGeom then
#      Print("  Before call to FindGeometricallyUniqueSolutionLP\n");
      eVect:=FindGeometricallyUniqueSolutionToLinearProgramming(ListIneq, ToBeMinimized);
#      Print("  After call to FindGeometricallyUniqueSolutionLP\n");
      TheFunc:=NullMat(n+1,n+1);
      for i in [1..pLin]
      do
        TheFunc:=TheFunc+eVect[i]*ListQuadFunc[i];
      od;
      if First(EXTinput, x->x*TheFunc*x<1)<>fail then
        Error("Inconsistency in TheFunc");
      fi;
      TheFuncInt:=RemoveFractionMatrix(TheFunc);
    fi;
    IsDone:=false;
    #
    # QuadForm not of full rank
    #
    if IsDone=false then
      if RankMat(TheQuadForm)<n then
        for eNSP in NullspaceMat(TheQuadForm)
        do
          eVert:=Concatenation([0], eNSP);
          Add(EXTinput, eVert);
        od;
        IsDone:=true;
      fi;
    fi;
    #
    # Heuristic method for finding a point of negative value
    #
    DoHeuristic:=true;
    if IsDone=false and DoHeuristic=true then
      eRecMin:=InfDel_GetRealMinimalPoint(TheFunc);
      if eRecMin.success then
        if eRecMin.eValInt < 0 then
          NewVert:=Concatenation([1], eRecMin.xCentInt);
          if Position(EXT, NewVert)<>fail then
            Error("a point of negative value should not be in EXT (which are at 0 value)");
          fi;
          Add(EXTinput, NewVert);
          IsDone:=true;
        fi;
      fi;
    fi;
    #
    # The QuadForm is not positive definite
    #
    if IsDone=false then
      if IsPositiveSymmetricMatrix(TheQuadForm)=false then
        NewVect:=GetNonPositiveVector(TheQuadForm);
        eLimitEXT:=Concatenation([0], NewVect);
        Print("  eLimitEXT=", eLimitEXT, "\n");
        Add(EXTinput, eLimitEXT);
        IsDone:=true;
      fi;
    fi;
    #
    # The QuadForm is not positive definite
    #
    if IsDone=false then
      TheCVP:=InfDel_GetNegCVPVector(TheFuncInt, TheDelaunay);
      if TheCVP.TheResult=false then
        Print("  TheCVP.ListVect=", TheCVP.ListVect, "\n");
        for NewVert in TheCVP.ListVect
        do
          if Position(EXT, NewVert)=fail then
            Add(EXTinput, NewVert);
            IsDone:=true;
          else
            Add(ListDeny, rec(case:="InfDel_GetNegCVPVector", NewVert:=NewVert));
          fi;
        od;
      fi;
    fi;
    #
    # Finding points of negative values
    #
    if IsDone=false then
      TheReply:=InfDel_GetZeroSetKernel(TheFuncInt);
      if IsBound(TheReply.error)=true then
        if TheReply.error="There are points with negative value at integral points" then
          UpperLimit:=10000;
          ListVect:=GetAllNegativePoints(TheFuncInt, UpperLimit);
          ListVert:=[];
          for NewVect in ListVect
          do
            NewVert:=Concatenation([1], NewVect);
            if Position(EXT, NewVert)=fail then
              Add(ListVert, NewVert);
            else
              Add(ListDeny, rec(case:="GetAllNegativePoints", NewVert:=NewVert));
            fi;
          od;
          ListNorm:=List(ListVert, Vect_L1norm);
          MinNorm:=Minimum(ListNorm);
          posVert:=First([1..Length(ListVert)], x->ListNorm[x]=MinNorm);
          OptChoice:=2;
          if OptChoice=1 then
            Add(EXTinput, ListVert[posVert]);
          else
            Append(EXTinput, ListVert);
          fi;
          if Length(ListVect)=UpperLimit then
            ListVect:=GetLowestPoints(TheFuncInt);
            ListVert:=List(ListVect, x->Concatenation([1], x));
            Add(EXTinput, ListVert[1]);
          fi;
        else
          Error("Other error cases should not happen");
        fi;
      fi;
      if IsBound(TheReply.error)=false then
        if Length(TheReply.TheRec.VectSpace)>0 then
          Error("VectSpace should be trivial since the matrix is positive definite");
        fi;
        if Set(TheReply.TheRec.EXT)<>Set(EXT) then
          TheDiff:=Difference(Set(TheReply.TheRec.EXT), Set(EXT));
          Append(EXTinput, TheDiff);
        else
          break;
        fi;
      fi;
    fi;
    #
    # Reduction of the size of the point set.
    #
    DoReduction:=true;
    if DoReduction then
      IdxSel:=Filtered([1..Length(EXTinput)], x->EXTinput[x]*TheFunc*EXTinput[x]<=1);
      EXTinput:=EXTinput{IdxSel};
    fi;
  od;
  Print("End of TestRealizabilityDelaunay_Space\n");
  return rec(reply:=true, TheFunc:=TheFunc);
end;

KernelTestRealizabilityDelaunay:=function(EXT)
  local TheBasis;
  TheBasis:=GetInvariantSymmetricMatrixBasis(EXT);
  return TestRealizabilityDelaunay_Space(EXT, TheBasis);
end;


TestRealizabilityDelaunay:=function(EXT)
  local nbVert, n, eDiff, ListDiff, iVert, eDiffVert, eVect, NSP, eBasis, fDiffVert, fVect, nBasis, EXTred, eSol, eVertRed, TheSol, nRed, Qmat, vVect, xMin, eBasisChange, eInvMat, alpha, Fmat, i, j, lAff, f0, TheFuncRet, TheQuadForm, eVal, TheRec, rnk, TheDet, eVert, eNorm, TheReply;
  nbVert:=Length(EXT);
  n:=Length(EXT[1])-1;
  if n<4 then
    return KernelTestRealizabilityDelaunay(EXT);
  fi;
  for i in [1..nbVert]
  do
    eDiff:=Difference([1..nbVert], [i]);
    ListDiff:=[];
    for iVert in [2..Length(eDiff)]
    do
      eDiffVert:=EXT[eDiff[iVert]] - EXT[eDiff[1]];
      eVect:=eDiffVert{[2..n+1]};
      Add(ListDiff, eVect);
    od;
    rnk:=RankMat(ListDiff);
    Print("i=", i, " rnk=", rnk, "\n");
    if rnk=n-1 then
      NSP:=RemoveFractionMatrix(NullspaceMat(TransposedMat(ListDiff)));
      eBasis:=NullspaceIntMat(TransposedMat(NSP));
      fDiffVert:=EXT[i] - EXT[eDiff[1]];
      fVect:=fDiffVert{[2..n+1]};
      nBasis:=Concatenation(eBasis, [fVect]);
      TheDet:=AbsInt(DeterminantMat(nBasis));
      Print("  TheDet=", TheDet, "\n");
      if TheDet=1 then
        EXTred:=[];
        for iVert in eDiff
        do
          eDiffVert:=EXT[iVert] - EXT[eDiff[1]];
          eVect:=eDiffVert{[2..n+1]};
          eSol:=SolutionIntMat(eBasis, eVect);
          if eSol=fail then
            Error("Consistency error");
          fi;
          eVertRed:=Concatenation([1], eSol);
          Add(EXTred, eVertRed);
        od;
        TheSol:=TestRealizabilityDelaunay(EXTred);
        if TheSol.reply=false then
          return rec(reply:=false);
        fi;
        nRed:=n-1;
        Qmat:=List(TheSol.TheFunc{[2..nRed+1]}, x->x{[2..nRed+1]});
        vVect:=TheSol.TheFunc[1]{[2..nRed+1]};
        xMin:=-vVect*Inverse(Qmat);
        eBasisChange:=[EXT[eDiff[1]]];
        for eVect in eBasis
        do
          Add(eBasisChange, Concatenation([0], eVect));
        od;
        Add(eBasisChange, Concatenation([0], fVect));
        eInvMat:=Inverse(eBasisChange);
        alpha:=1;
        while(true)
        do
          Fmat:=NullMat(n+1,n+1);
          for i in [1..n]
          do
            for j in [1..n]
            do
              Fmat[i][j]:=TheSol.TheFunc[i][j];
            od;
          od;
          lAff:=TheSol.TheFunc[1]{[2..nRed+1]};
          for i in [1..n-1]
          do
            eVal:= - lAff[i];
            Fmat[n+1][i+1]:=eVal;
            Fmat[i+1][n+1]:=eVal;
          od;
          f0:=(-alpha - Fmat[1][1])/2;
          Fmat[1][n+1]:=f0;
          Fmat[n+1][1]:=f0;
          Fmat[n+1][n+1]:=alpha;
          TheFuncRet:=eInvMat*Fmat*TransposedMat(eInvMat);
          for eVert in EXT
          do
            eNorm:=eVert*TheFuncRet*eVert;
            if eNorm<>0 then
              Error("All points should be zeros");
            fi;
          od;
          TheQuadForm:=List(TheFuncRet{[2..n+1]}, x->x{[2..n+1]});
          if IsPositiveDefiniteSymmetricMatrix(TheQuadForm) then
            TheReply:=InfDel_GetZeroSetKernel(TheFuncRet);
            if IsBound(TheReply.error)=false then
              TheRec:=TheReply.TheRec;
              if Set(TheRec.EXT)=Set(EXT) then
                return rec(reply:=true, TheFunc:=TheFuncRet);
              fi;
            fi;
          fi;
          alpha:=alpha+1;
        od;
      fi;
    fi;
  od;
  return KernelTestRealizabilityDelaunay(EXT);
end;
