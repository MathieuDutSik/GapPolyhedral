TestConjugacyInvolution:=function(g1, g2)
  local n, SPplus1, SPminus1, SPplus2, SPminus2, eBasis1, eBasis2, eDet1, eDet2, eConj;
  n:=Length(g1);
  if g1*g1<>IdentityMat(n) then
    return fail;
  fi;
  if g2*g2<>IdentityMat(n) then
    return false;
  fi;
  SPplus1:=NullspaceIntMat(g1 + IdentityMat(n));
  SPplus2:=NullspaceIntMat(g2 + IdentityMat(n));
  SPminus1:=NullspaceIntMat(g1 - IdentityMat(n));
  SPminus2:=NullspaceIntMat(g2 - IdentityMat(n));
  if Length(SPplus1)<>Length(SPplus2) then
    return false;
  fi;
  if Length(SPminus1)<>Length(SPminus2) then
    return false;
  fi;
  eBasis1:=Concatenation(SPplus1, SPminus1);
  eBasis2:=Concatenation(SPplus2, SPminus2);
  eDet1:=AbsInt(DeterminantMat(eBasis1));
  eDet2:=AbsInt(DeterminantMat(eBasis2));
  if eDet1<>eDet2 then
    return false;
  fi;
  if eDet1<>1 then
    return fail;
  fi;
  eConj:=Inverse(eBasis1)*eBasis2;
  if Inverse(eConj)*g1*eConj<>g2 then
    Error("Bug that needs to be solved");
  fi;
  return eConj;
end;

GetInvConjClassElement:=function(eElt)
  local SpaceAntisymInv, SpaceSymInv, eOrder, eBravais, eCoeffChar, ePol, eCoeffMin;
  SpaceAntisymInv:=InvariantAntisymmetricForm([eElt]);
  SpaceSymInv:=InvariantFormDutourVersion([eElt]);
  eOrder:=Order(eElt);
  eBravais:=BravaisGroup(Group([eElt]));
  ePol:=CharacteristicPolynomial(eElt);
  eCoeffChar:=CoefficientsOfUnivariatePolynomial(ePol);
  ePol:=MinimalPolynomial(eElt);
  eCoeffMin:=CoefficientsOfUnivariatePolynomial(ePol);
  return rec(SymDim:=Length(SpaceSymInv),
             AntisymDim:=Length(SpaceAntisymInv),
             eOrder:=eOrder,
             eCoeffChar:=eCoeffChar, 
             eCoeffMin:=eCoeffMin, 
             BravaisSize:=Order(eBravais));
end;


TestConjugacyElementDirect:=function(g1, g2)
  local eGRP1, eGRP2, n, eEquiv, ListGen1conj, eGRP1conj, g1conj, TheNorm, TheAction, eRec, nbCos, iCos, eRet;
  n:=Length(g1);
  Print("TestConjugacyElementDirect, n=", n, "\n");
  if Length(g1)<>Length(g2) then
    return false;
  fi;
  if g1=g2 then
    return IdentityMat(n);
  fi;
  if Length(g1)=1 then
    if g1[1][1]<>g2[1][1] then
      return false;
    fi;
    return [[1]];
  fi;
  if GetInvConjClassElement(g1)<>GetInvConjClassElement(g2) then
    return false;
  fi;
  eGRP1:=BravaisGroup(Group([g1]));
  eGRP2:=BravaisGroup(Group([g2]));
  eEquiv:=RepresentativeAction(GL(n, Integers), eGRP1, eGRP2);
  if eEquiv=fail then
    return false;
  fi;
  ListGen1conj:=List(GeneratorsOfGroup(eGRP1), x->Inverse(eEquiv)*x*eEquiv);
  eGRP1conj:=Group(ListGen1conj);
  if eGRP1conj<>eGRP2 then
    Error("We have some conjugation error");
  fi;
  g1conj:=Inverse(eEquiv)*g1*eEquiv;
  TheNorm:=NormalizerInGLnZBravaisGroup(eGRP2);
  TheAction:=function(x, g)
    return Inverse(g)*x*g;
  end;
  eRec:=OrbitWithAction(TheNorm, g1conj, TheAction);
  nbCos:=Length(eRec.ListCoset);
  for iCos in [1..nbCos]
  do
    if eRec.ListCoset[iCos]=g2 then
      eRet:=eEquiv*eRec.ListElement[iCos];
      if Inverse(eRet)*g1*eRet<>g2 then
        Error("We have a bug to solve");
      fi;
      return eRet;
    fi;
  od;
  return false;
end;

GetOrthSpace:=function(g, eBasis)
  local n, SpaceSymInv, ListEqua, eMat, eVect, TheOrth;
  n:=Length(g);
  SpaceSymInv:=InvariantFormDutourVersion([g]);
  ListEqua:=[];
  for eMat in SpaceSymInv
  do
    for eVect in eBasis
    do
      Add(ListEqua, eVect*eMat);
    od;
  od;
  if Length(ListEqua)=0 then
    return IdentityMat(n);
  else
    TheOrth:=NullspaceIntMat(TransposedMat(ListEqua));
  fi;
  Print("|SpaceSymInv|=", Length(SpaceSymInv), " |TheOrth|=", Length(TheOrth), "\n");
  return TheOrth;
end;



ReductionSpacePlusMinus:=function(g1, g2)
  local n, SPplus1, SPplus2, SPminus1, SPminus2, eBasis1, eBasis2, NSP1, NSP2, eSpace1, eSpace2, eSol1, eSol2, eDet1, eDet2, eBasisTot1, eBasisTot2, eDetTot1, eDetTot2, gSec1, gSec2, dimR, gRed1, gRed2, gBlockA1, gBlockA2, gBlockB1, gBlockB2, eTest, BigMat, i, j, eRetMat, NSPorth1, NSPorth2;
  n:=Length(g1);
  SPplus1:=NullspaceIntMat(g1 + IdentityMat(n));
  SPplus2:=NullspaceIntMat(g2 + IdentityMat(n));
  SPminus1:=NullspaceIntMat(g1 - IdentityMat(n));
  SPminus2:=NullspaceIntMat(g2 - IdentityMat(n));
  eBasis1:=Concatenation(SPplus1, SPminus1);
  eBasis2:=Concatenation(SPplus2, SPminus2);
  if Length(SPplus1)<>Length(SPplus2) then
    return false;
  fi;
  if Length(SPminus1)<>Length(SPminus2) then
    return false;
  fi;
  if Length(eBasis1)=0 then
    return fail;
  fi;
  NSP1:=NullspaceIntMat(TransposedMat(eBasis1));
  NSP2:=NullspaceIntMat(TransposedMat(eBasis2));
  if Length(NSP1)=0 then
    return fail;
  fi;
  eSpace1:=NullspaceIntMat(TransposedMat(NSP1));
  eSpace2:=NullspaceIntMat(TransposedMat(NSP2));
  eSol1:=List(eBasis1, x->SolutionMat(eSpace1, x));
  eSol2:=List(eBasis2, x->SolutionMat(eSpace2, x));
  eDet1:=AbsInt(DeterminantMat(eSol1));
  eDet2:=AbsInt(DeterminantMat(eSol2));
  if eDet1 <> eDet2 then
    return false;
  fi;
  if eDet1<>1 then
    return fail;
  fi;
  NSPorth1:=GetOrthSpace(g1, eBasis1);
  NSPorth2:=GetOrthSpace(g2, eBasis2);
  eBasisTot1:=Concatenation(NSPorth1, eBasis1);
  eBasisTot2:=Concatenation(NSPorth2, eBasis2);
  eDetTot1:=AbsInt(DeterminantMat(eBasisTot1));
  eDetTot2:=AbsInt(DeterminantMat(eBasisTot2));
  if eDetTot1 <>1 or eDetTot2 <> 1 then
    Print("CASS 2 eDetTot1=", eDetTot1, " eDetTot2=", eDetTot2, "\n");
    return fail;
  fi;
  gSec1:=eBasisTot1*g1*Inverse(eBasisTot1);
  gSec2:=eBasisTot2*g2*Inverse(eBasisTot2);
  dimR:=Length(NSPorth1);
  gRed1:=List(gSec1{[1..dimR]}, x->x{[1..dimR]});
  gRed2:=List(gSec2{[1..dimR]}, x->x{[1..dimR]});
  gBlockA1:=List(gSec1{[dimR+1..n]}, x->x{[1..dimR]});
  gBlockA2:=List(gSec2{[dimR+1..n]}, x->x{[1..dimR]});
  gBlockB1:=List(gSec1{[1..dimR]}, x->x{[dimR+1..n]});
  gBlockB2:=List(gSec2{[1..dimR]}, x->x{[dimR+1..n]});
  if gBlockA1<>NullMat(n-dimR, dimR) or gBlockA2<>NullMat(n-dimR, dimR) then
    Error("We have a matrix error");
  fi;
  if gBlockB1<>NullMat(dimR, n-dimR) or gBlockB1<>NullMat(dimR, n-dimR) then
    return fail;
  fi;
  eTest:=TestConjugacyElementDirect(gRed1, gRed2);
  if eTest=false then
    return fail;
  fi;
  BigMat:=IdentityMat(n,n);
  for i in [1..dimR]
  do
    for j in [1..dimR]
    do
      BigMat[i][j]:=eTest[i][j];
    od;
  od;
  eRetMat:=Inverse(eBasisTot1)*BigMat*eBasisTot2;
  return eRetMat;
end;


UseInvariantSpaces:=function(g1, g2, ListInv1, ListInv2)
  local n, eBasisTot1, eFam, eBasisTot2, eDet1, eDet2, ListDim1, ListDim2, ListDim, gSec1, gSec2, eBigMat, eShift, iDim, eDim, eBegin, eEnd, eRedmat1, eRedmat2, eTest, i, j, eRetMat;
  n:=Length(g1);
  eBasisTot1:=[];
  for eFam in ListInv1
  do
    Append(eBasisTot1, eFam);
  od;
  eBasisTot2:=[];
  for eFam in ListInv2
  do
    Append(eBasisTot2, eFam);
  od;
  eDet1:=AbsInt(DeterminantMat(eBasisTot1));
  eDet2:=AbsInt(DeterminantMat(eBasisTot2));
  Print("eDet1=", eDet1, " eDet2=", eDet2, "\n");
  if eDet1<>eDet2 then
    return false;
  fi;
  if eDet1<>1 then
    return fail;
  fi;
  ListDim1:=List(ListInv1, Length);
  ListDim2:=List(ListInv2, Length);
  if ListDim1<>ListDim2 then
    return false;
  fi;
  ListDim:=ListDim1;
  gSec1:=eBasisTot1*g1*Inverse(eBasisTot1);
  gSec2:=eBasisTot2*g2*Inverse(eBasisTot2);
  eBigMat:=NullMat(n,n);
  eShift:=0;
  for iDim in [1..Length(ListDim)]
  do
    eDim:=ListDim[iDim];
    eBegin:=eShift+1;
    eEnd:=eShift+eDim;
    eRedmat1:=List(gSec1{[eBegin..eEnd]}, x->x{[eBegin..eEnd]});
    eRedmat2:=List(gSec2{[eBegin..eEnd]}, x->x{[eBegin..eEnd]});
    eTest:=TestConjugacyElementDirect(eRedmat1, eRedmat2);
    if eTest=false then
      return false;
    fi;
    for i in [1..eDim]
    do
      for j in [1..eDim]
      do
        eBigMat[i+eShift][j+eShift]:=eTest[i][j];
      od;
    od;
    eShift:=eShift+eDim;
  od;
  eRetMat:=Inverse(eBasisTot1)*eBigMat*eBasisTot2;
  return eRetMat;
end;



ReductionSpacePlusMinus:=function(g1, g2)
  local n, eVal, eSpace1, eSpace2, eOrth1, eOrth2, ListInv1, ListInv2, eReply;
  n:=Length(g1);
  for eVal in [1, -1]
  do
    eSpace1:=NullspaceIntMat(g1 + eVal*IdentityMat(n));
    eSpace2:=NullspaceIntMat(g2 + eVal*IdentityMat(n));
    if Length(eSpace1)<>Length(eSpace2) then
      return false;
    fi;
    if Length(eSpace1)>0 then
      eOrth1:=GetOrthSpace(g1, eSpace1);
      eOrth2:=GetOrthSpace(g2, eSpace2);
      Print("|eSpace1|=", Length(eSpace1), " |eOrth1|=", Length(eOrth1), "\n");
      Print("|eSpace2|=", Length(eSpace2), " |eOrth2|=", Length(eOrth2), "\n");
      ListInv1:=[eSpace1, eOrth1];
      ListInv2:=[eSpace2, eOrth2];
      eReply:=UseInvariantSpaces(g1, g2, ListInv1, ListInv2);
      if eReply<>fail then
        return eReply;
      fi;
    fi;
  od;
  return fail;
end;




UseInvariantSpacesNoFail:=function(g1, g2, ListInv1, ListInv2, ListCommSp1)
  local n, eBasisTot1, eFam, eBasisTot2, eDet1, eDet2, ListDim1, ListDim2, ListDim, gSec1, gSec2, eBigMat, eShift, iDim, eDim, eBegin, eEnd, eRedmat1, eRedmat2, eTest, i, j, eSolMat, eGenCommRat, ListGenRatComm1, ListShift, eGen, eMat, eCommMat, iEquiv, SpaceMethod, IterativeMethod, ListGenRatCommCan1;
  Print("Begin UseInvariantSpaceNoFail\n");
  n:=Length(g1);
  eBasisTot1:=[];
  for eFam in ListInv1
  do
    Append(eBasisTot1, eFam);
  od;
  eBasisTot2:=[];
  for eFam in ListInv2
  do
    Append(eBasisTot2, eFam);
  od;
  eDet1:=AbsInt(DeterminantMat(eBasisTot1));
  eDet2:=AbsInt(DeterminantMat(eBasisTot2));
  Print("eDet1=", eDet1, " eDet2=", eDet2, "\n");
  if eDet1<>eDet2 then
    return false;
  fi;
  ListDim1:=List(ListInv1, Length);
  ListDim2:=List(ListInv2, Length);
  if ListDim1<>ListDim2 then
    return false;
  fi;
  ListDim:=ListDim1;
  gSec1:=eBasisTot1*g1*Inverse(eBasisTot1);
  gSec2:=eBasisTot2*g2*Inverse(eBasisTot2);
  eBigMat:=NullMat(n,n);
  eShift:=0;
  ListShift:=ListWithIdenticalEntries(Length(ListDim), 0);
  for iDim in [1..Length(ListDim)]
  do
    eDim:=ListDim[iDim];
    eBegin:=eShift+1;
    eEnd:=eShift+eDim;
    eRedmat1:=List(gSec1{[eBegin..eEnd]}, x->x{[eBegin..eEnd]});
    eRedmat2:=List(gSec2{[eBegin..eEnd]}, x->x{[eBegin..eEnd]});
    eTest:=TestConjugacyElementDirect(eRedmat1, eRedmat2);
    if eTest=false then
      return false;
    fi;
    for i in [1..eDim]
    do
      for j in [1..eDim]
      do
        eBigMat[i+eShift][j+eShift]:=eTest[i][j];
      od;
    od;
    ListShift[iDim]:=eShift;
    eShift:=eShift+eDim;
  od;
  eSolMat:=Inverse(eBasisTot1)*eBigMat*eBasisTot2;
  #
  ListGenRatComm1:=[];
  ListGenRatCommCan1:=[];
  for iDim in [1..Length(ListDim)]
  do
    eShift:=ListShift[iDim];
    eDim:=ListDim[iDim];
    for eGen in GeneratorsOfGroup(ListCommSp1[iDim])
    do
      eMat:=IdentityMat(n);
      for i in [1..eDim]
      do
        for j in [1..eDim]
        do
          eMat[eShift+i][eShift+j]:=eGen[i][j];
        od;
      od;
      eCommMat:=Inverse(eBasisTot1)*eMat*eBasisTot1;
      if g1*eCommMat<>eCommMat*g1 then
        Error("Big Error 1");
      fi;
      Add(ListGenRatCommCan1, eMat);
#      Print("det(eCommMat)=", DeterminantMat(eCommMat), "\n");
      Add(ListGenRatComm1, eCommMat);
    od;
  od;
  #
  IterativeMethod:=function()
    local ListEquiv, ListStatus, FuncInsert, IsFinished, len, i, eGenCommRat, eNewEquiv;
    ListEquiv:=[eSolMat];
    ListStatus:=[0];
    if IsIntegralMat(eSolMat) then
      return eSolMat;
    fi;
    FuncInsert:=function(eEquiv)
      local iEquiv, eTestMat;
      for iEquiv in [1..Length(ListEquiv)]
      do
        eTestMat:=Inverse(eEquiv)*ListEquiv[iEquiv];
        if eTestMat*g2<>g2*eTestMat then
          Error("Big Error 2");
        fi;
        if IsIntegralMat(eTestMat) then
          return;
        fi;
      od;
      Add(ListEquiv, eEquiv);
      Add(ListStatus, 0);
    end;
    while(true)
    do
      IsFinished:=true;
      len:=Length(ListEquiv);
      for i in [1..len]
      do
        if ListStatus[i]=0 then
          IsFinished:=false;
          ListStatus[i]:=1;
          for eGenCommRat in ListGenRatComm1
          do
            eNewEquiv:=eGenCommRat*ListEquiv[i];
            if IsIntegralMat(eNewEquiv) then
              return eNewEquiv;
            fi;
            FuncInsert(eNewEquiv);
          od;
        fi;
      od;
      if IsFinished then
        break;
      fi;
      Print("|ListEquiv|=", Length(ListEquiv), "\n");
      return false;
    od;
  end;
  SpaceMethod:=function()
    local eMat1, eMat2, eRec1, eRec2, GRPmatr, eEquiv, eRetMat;
    eMat1:=Inverse(eBasisTot1);
    eMat2:=Inverse(eBasisTot2)*Inverse(eBigMat);
    eRec1:=RemoveFractionMatrixPlusCoef(eMat1);
    eRec2:=RemoveFractionMatrixPlusCoef(eMat2);
    if eRec1.TheMult<>eRec2.TheMult then
      return false;
    fi;
    GRPmatr:=Group(ListGenRatCommCan1);
    eEquiv:=LinearSpace_Equivalence(GRPmatr, eRec1.TheMat, eRec2.TheMat);
    if eEquiv=fail then
      return false;
    fi;
    eRetMat:=Inverse(eBasisTot1)*eEquiv*eBigMat*eBasisTot2;
    if Inverse(eRetMat)*g1*eRetMat<>g2 then
      Error("We have more bugs left to solve");
    fi;
    return eRetMat;
  end;
  return SpaceMethod();
#  return IterativeMethod();
end;


MinimalBreakerNoFail:=function(g1, g2)
  local n, GetSpaceDecomp, ListInv1, ListInv2;
  n:=Length(g1);  
  GetSpaceDecomp:=function(g)
    local eSpaceP, eSpaceM, eOrth;
    eSpaceP:=NullspaceIntMat(g - IdentityMat(n));
    eSpaceM:=NullspaceIntMat(g + IdentityMat(n));
    eOrth:=GetOrthSpace(g, Concatenation(eSpaceP, eSpaceM));
    return [eSpaceP, eSpaceM, eOrth];
  end;
  ListInv1:=GetSpaceDecomp(g1);
  ListInv2:=GetSpaceDecomp(g2);

end;



ReductionSpacePlusMinusNoFail:=function(g1, g2)
  local n, GetSpaceDecomp, ListInv1, ListInv2, ListCommSp1, eRedMat, PreListInv1, PreListInv2;
  n:=Length(g1);
  GetSpaceDecomp:=function(g)
    local eSpaceP, eSpaceM, eOrth;
    eSpaceP:=NullspaceIntMat(g - IdentityMat(n));
    eSpaceM:=NullspaceIntMat(g + IdentityMat(n));
    eOrth:=GetOrthSpace(g, Concatenation(eSpaceP, eSpaceM));
    return [eSpaceP, eSpaceM, eOrth];
  end;
  PreListInv1:=GetSpaceDecomp(g1);
  PreListInv2:=GetSpaceDecomp(g2);
  ListInv1:=Filtered(PreListInv1, x->Length(x)>0);
  ListInv2:=Filtered(PreListInv2, x->Length(x)>0);
  ListCommSp1:=[];
  if Length(PreListInv1[1])>0 then
    Add(ListCommSp1, GL(Length(PreListInv1[1]), Integers) );
  fi;
  if Length(PreListInv1[2])>0 then
    Add(ListCommSp1, GL(Length(PreListInv1[2]), Integers) );
  fi;
  if Length(PreListInv1[3])>0 then
    eRedMat:=List(PreListInv1[3], x->SolutionIntMat(PreListInv1[3], x*g1));
    Add(ListCommSp1, CentralizerInGLnZ(Group([eRedMat])));
  fi;
  return UseInvariantSpacesNoFail(g1, g2, ListInv1, ListInv2, ListCommSp1);
end;





GetMinimalBlocks:=function(g)
  local n, GRA, i, j, LConn;
  n:=Length(g);
  GRA:=NullGraph(Group(()), n);
  for i in [1..n]
  do
    for j in [1..n]
    do
      if i<>j then
        if g[i][j]<>0 or g[j][i]<>0 then
          AddEdgeOrbit(GRA, [i,j]);
          AddEdgeOrbit(GRA, [j,i]);
        fi;
      fi;
    od;
  od;
  LConn:=ConnectedComponents(GRA);
  return LConn;
end;


FunctionByBlock:=function(g1, g2, LBlock1, LBlock2)
  local n, eType1, eType2, nbConn, TheBigMat, ePermMat, ListRec, iBlock1, eBlock1, len, RedMat1, IsDone, iBlock2, eBlock2, RedMat2, eTest, i, j, g1_conj, eRetMat, hMat, eRec, nbBlock, ListStatus, iBlock, LBlockSel1, LBlockSel2;
  LBlockSel1:=Filtered(LBlock1, x->Length(x)>0);
  LBlockSel2:=Filtered(LBlock2, x->Length(x)>0);
  eType1:=Collected(List(LBlockSel1, Length));
  eType2:=Collected(List(LBlockSel2, Length));
  if eType1<>eType2 then
    return fail;
  fi;
  n:=Length(g1);
  nbBlock:=Length(LBlockSel1);
  TheBigMat:=NullMat(n, n);
  ePermMat:=NullMat(n,n);
  ListRec:=[];
  ListStatus:=ListWithIdenticalEntries(nbBlock,0);
  for iBlock1 in [1..nbBlock]
  do
    eBlock1:=LBlockSel1[iBlock1];
    len:=Length(eBlock1);
    RedMat1:=List(g1{eBlock1}, x->x{eBlock1});
    IsDone:=false;
    for iBlock2 in [1..nbBlock]
    do
      if IsDone=false and ListStatus[iBlock2]=0 then
        eBlock2:=LBlockSel2[iBlock2];
        RedMat2:=List(g2{eBlock2}, x->x{eBlock2});
#        Print("RedMat1:=\n");
#        PrintArray(RedMat1);
#        Print("RedMat2:=\n");
#        PrintArray(RedMat2);
        eTest:=TestConjugacyElementDirect(RedMat1, RedMat2);
        if eTest<>false then
          ListRec[iBlock2]:=rec(iBlock1:=iBlock1, iBlock2:=iBlock2, RedMat1:=RedMat1, RedMat2:=RedMat2, eTest:=eTest);
          IsDone:=true;
          ListStatus[iBlock2]:=iBlock1;
          for i in [1..len]
          do
            ePermMat[ eBlock1[i] ][ eBlock2[i] ]:=1;
          od;
        fi;
      fi;
    od;
    if IsDone=false then
      return fail;
    fi;
  od;
  g1_conj:=Inverse(ePermMat)*g1*ePermMat;
  hMat:=NullMat(n,n);
  for iBlock in [1..nbBlock]
  do
    eRec:=ListRec[iBlock];
    eBlock2:=LBlockSel2[iBlock];
    RedMat1:=List(g1_conj{eBlock2}, x->x{eBlock2});
    RedMat2:=List(g2{eBlock2}, x->x{eBlock2});
    if eRec.RedMat1<>RedMat1 then
      Error("Error in RedMat1");
    fi;
    if eRec.RedMat2<>RedMat2 then
      Error("Error in RedMat2");
    fi;
    len:=Length(eBlock2);
    for i in [1..len]
    do
      for j in [1..len]
      do
        hMat[ eBlock2[i] ][ eBlock2[j] ]:=eRec.eTest[i][j];
      od;
    od;
  od;
  eRetMat:=ePermMat*hMat;
  if Inverse(eRetMat)*g1*eRetMat<>g2 then
    Error("Error in the conjugation for DiagnoalRedutionPlusMinus");
  fi;
  return eRetMat;
end;





TestConjugacyDiagonalByBlock:=function(g1, g2)
  local n, LConn1, LConn2, eType1, eType2, nbConn, ListStatus, TheBigMat, iConn1, eConn1, len, RedMat1, IsDone, iConn2, eConn2, RedMat2, eTest, eTestInv, i, j, iB, jB, eRetMat, hMat, g1_conj, ePermMat, ListRec, eRec;
  n:=Length(g1);
  LConn1:=GetMinimalBlocks(g1);
  LConn2:=GetMinimalBlocks(g2);
  eType1:=Collected(List(LConn1, Length));
  eType2:=Collected(List(LConn2, Length));
  if eType1<>eType2 then
    return fail;
  fi;
  return FunctionByBlock(g1, g2, LConn1, LConn2);
end;



DiagonalReductionPlusMinus:=function(g1, g2)
  local n, LConn1, LConn2, eType1, eType2, nbConn, ListStatus, TheBigMat, iConn1, eConn1, len, RedMat1, IsDone, iConn2, eConn2, RedMat2, eTest, eTestInv, i, j, iB, jB, eRetMat, hMat, g1_conj, ePermMat, ListRec, eRec, idx, eVal, ListPlus1, ListPlus2, ListMinus1, ListMinus2, eDiff1, eDiff2, eConn, LConnRed1, LConnRed2, iConn, eSetPlus1, eSetMinus1, eSetPlus2, eSetMinus2, nbMinus, nbPlus;
  n:=Length(g1);
  LConn1:=GetMinimalBlocks(g1);
  LConn2:=GetMinimalBlocks(g2);
  Print("LConn1=", LConn1, "\n");
  Print("LConn2=", LConn2, "\n");
  ListPlus1:=[];
  ListMinus1:=[];
  for eConn in LConn1
  do
    if Length(eConn)=1 then
      idx:=eConn[1];
      eVal:=g1[idx][idx];
      if eVal=1 then
        Add(ListPlus1, idx);
      else
        if eVal=-1 then
          Add(ListMinus1, idx);
        else
          Error("Error for g1");
        fi;
      fi;
    fi;
  od;
  ListPlus2:=[];
  ListMinus2:=[];
  for eConn in LConn2
  do
    if Length(eConn)=1 then
      idx:=eConn[1];
      eVal:=g2[idx][idx];
      if eVal=1 then
        Add(ListPlus2, idx);
      else
        if eVal=-1 then
          Add(ListMinus2, idx);
        else
          Error("Error for g2");
        fi;
      fi;
    fi;
  od;
  nbPlus:=Minimum(Length(ListPlus1), Length(ListPlus2));
  nbMinus:=Minimum(Length(ListMinus1), Length(ListMinus2));
  if nbPlus=0 and nbMinus=0 then
    return fail;
  fi;
  eSetPlus1:=ListPlus1{[1..nbPlus]};
  eSetPlus2:=ListPlus2{[1..nbPlus]};
  eSetMinus1:=ListMinus1{[1..nbMinus]};
  eSetMinus2:=ListMinus2{[1..nbMinus]};
  eDiff1:=Difference([1..n], Set(Union(eSetPlus1, eSetMinus1)));
  eDiff2:=Difference([1..n], Set(Union(eSetPlus2, eSetMinus2)));
  LConnRed1:=[eSetPlus1, eSetMinus1, eDiff1];
  LConnRed2:=[eSetPlus2, eSetMinus2, eDiff2];
  return FunctionByBlock(g1, g2, LConnRed1, LConnRed2);
end;


DiagonalReductionPlusMinusMatchBlock:=function(g1, g2)
  local n, LConn1, LConn2, eType1, eType2, eConn, idx, eVal, ListPlus1, ListMinus1, ListPlus2, ListMinus2, nbPlus, nbMinus, eUnion1, eUnion2, LConnSel1, LConnSel2, nbPart1, nbPart2, LBlock1, LBlock2, test, GetBlock, eSetPlus1, eSetMinus1, eSetPlus2, eSetMinus2, ePart1, ePart2, LPart1, LPart2;
  n:=Length(g1);
  LConn1:=GetMinimalBlocks(g1);
  LConn2:=GetMinimalBlocks(g2);
  Print("LConn1=", LConn1, "\n");
  Print("LConn2=", LConn2, "\n");
  ListPlus1:=[];
  ListMinus1:=[];
  for eConn in LConn1
  do
    if Length(eConn)=1 then
      idx:=eConn[1];
      eVal:=g1[idx][idx];
      if eVal=1 then
        Add(ListPlus1, idx);
      else
        if eVal=-1 then
          Add(ListMinus1, idx);
        else
          Error("Error for g1");
        fi;
      fi;
    fi;
  od;
  ListPlus2:=[];
  ListMinus2:=[];
  for eConn in LConn2
  do
    if Length(eConn)=1 then
      idx:=eConn[1];
      eVal:=g2[idx][idx];
      if eVal=1 then
        Add(ListPlus2, idx);
      else
        if eVal=-1 then
          Add(ListMinus2, idx);
        else
          Error("Error for g2");
        fi;
      fi;
    fi;
  od;
  nbPlus:=Minimum(Length(ListPlus1), Length(ListPlus2));
  nbMinus:=Minimum(Length(ListMinus1), Length(ListMinus2));
  Print("nbPlus=", nbPlus, "  nbMinus=", nbMinus, "\n");
  eSetPlus1:=ListPlus1{[1..nbPlus]};
  eSetPlus2:=ListPlus2{[1..nbPlus]};
  eSetMinus1:=ListMinus1{[1..nbMinus]};
  eSetMinus2:=ListMinus2{[1..nbMinus]};
  eUnion1:=Set(Union(eSetPlus1, eSetMinus1));
  eUnion2:=Set(Union(eSetPlus2, eSetMinus2));
  LConn1:=GetMinimalBlocks(g1);
  LConn2:=GetMinimalBlocks(g2);
  LConnSel1:=Filtered(LConn1, x->Length(Intersection(x, eUnion1))=0);
  LConnSel2:=Filtered(LConn2, x->Length(Intersection(x, eUnion2))=0);
  if Length(LConnSel1)=1 or Length(LConnSel2)=1 then
    return fail;
  fi;
  nbPart1:=Length(LConnSel1);
  nbPart2:=Length(LConnSel2);
  LPart1:=Difference(Set(FullListPartition(nbPart1)), [ [ [1..nbPart1] ] ]);
  LPart2:=Difference(Set(FullListPartition(nbPart2)), [ [ [1..nbPart2] ] ]);
  GetBlock:=function(eSetPlus, eSetMinus, LConnSel, ePart)
    local LBlock, eComp, fSet, eVal;
    LBlock:=[eSetPlus, eSetMinus];
    for eComp in ePart
    do
      fSet:=[];
      for eVal in eComp
      do
        fSet:=Union(fSet, LConnSel[eVal]);
      od;
      Add(LBlock, fSet);
    od;
    return LBlock;
  end;
  for ePart1 in LPart1
  do
    for ePart2 in LPart2
    do
#      Print("ePart1=", ePart1, "\n");
#      Print("ePart2=", ePart2, "\n");
      LBlock1:=GetBlock(eSetPlus1, eSetMinus1, LConnSel1, ePart1);
      LBlock2:=GetBlock(eSetPlus2, eSetMinus2, LConnSel2, ePart2);
#      Print("LBlock1=", LBlock1, "\n");
#      Print("LBlock2=", LBlock2, "\n");
      test:=FunctionByBlock(g1, g2, LBlock1, LBlock2);
      if test<>false and test<>fail then
        return test;
      fi;
    od;
  od;
  return fail;
end;




TestConjugacyElement:=function(g1, g2)
  local testInvol, testRed, testDiag, testDiagPM, testDiagPMblock, testDiagRedSpacePM, testRedSpaceNoFail, dimSymInv1, dimSymInv2, dimPM1, dimPM2, n;
  Print("g1=\n");
  PrintArray(g1);
  Print("g2=\n");
  PrintArray(g2);
  testInvol:=TestConjugacyInvolution(g1,g2);
  if testInvol<>fail then
    Print("testInvol success\n");
    return testInvol;
  fi;
  Print("testInvol fail\n");
  #
  testRed:=ReductionSpacePlusMinus(g1, g2);
  if testRed<>fail then
    Print("testRed success\n");
    return testRed;
  fi;
  Print("testRed fail\n");
  #
  testDiag:=TestConjugacyDiagonalByBlock(g1, g2);
  if testDiag<>fail then
    Print("testDiag success\n");
    return testDiag;
  fi;
  Print("testDiag fail\n");
  #
#  testDiagPM:=DiagonalReductionPlusMinus(g1, g2);
#  if testDiagPM<>fail then
#    Print("testDiagPM success\n");
#    return testDiagPM;
#  fi;
#  Print("testDiagPM fail\n");
  #
  #
  n:=Length(g1);
  dimPM1:=Length(NullspaceIntMat(g1 + IdentityMat(n))) + Length(NullspaceIntMat(g1 - IdentityMat(n)));
  dimPM2:=Length(NullspaceIntMat(g2 + IdentityMat(n))) + Length(NullspaceIntMat(g2 - IdentityMat(n)));
  Print("dimPM1=", dimPM1, "\n");
  if dimPM1<>dimPM2 then
    return false;
  fi;
  if dimPM1=0 then
    testDiagPMblock:=DiagonalReductionPlusMinusMatchBlock(g1, g2);
    if testDiagPMblock<>fail then
      Print("testDiagPMblock success\n");
      return testDiagPMblock;
    fi;
    Print("testDiagPMblock fail\n");
  fi;
  #
  if dimPM1>=4 then
    return ReductionSpacePlusMinusNoFail(g1, g2);
  fi;
  #
  dimSymInv1:=Length(InvariantFormDutourVersion([g1]));
  dimSymInv2:=Length(InvariantFormDutourVersion([g2]));
  Print("dimSymInv1=", dimSymInv1, "\n");
  if dimSymInv1<>dimSymInv2 then
    return false;
  fi;
  if dimSymInv1<=10 then
    return TestConjugacyElementDirect(g1, g2);
  else
    return ReductionSpacePlusMinusNoFail(g1, g2);
  fi;
end;


