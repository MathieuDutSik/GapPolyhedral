GetDependentTriple:=function(eSyst)
  local ListSets, eSet;
  ListSets:=[];
  for eSet in Combinations([1..Length(eSyst)], 3)
  do
    if RankMat(eSyst{eSet})=2 then
      Add(ListSets, eSet);
    fi;
  od;
  return ListSets;
end;







SymplecticStabilizer:=function(eSyst, FuncTestBelong)
  local n, eSystTotal, TheGRPperm, ListPermGens, ListMatrGens, TheGRPmatr, phi, TargetPermGrp, TargetListPermGens, TargetListMatrGens, FuncInsert, eElt, eMat, TargetMatrGrp;
  n:=Length(eSyst[1]);
  eSystTotal:=Concatenation(eSyst, -eSyst);
  TheGRPperm:=LinPolytope_Automorphism(eSystTotal);
  ListPermGens:=GeneratorsOfGroup(TheGRPperm);
  ListMatrGens:=List(ListPermGens, x->FindTransformation(eSystTotal, eSystTotal, x));
  TheGRPmatr:=Group(ListMatrGens);
  phi:=GroupHomomorphismByImagesNC(TheGRPperm, TheGRPmatr, ListPermGens, ListMatrGens);
  TargetPermGrp:=Group(());
  TargetListPermGens:=[];
  TargetListMatrGens:=[];
  FuncInsert:=function(eElt, eMat)
    if not(eElt in TargetPermGrp) then
      Add(TargetListPermGens, eElt);
      TargetPermGrp:=Group(TargetListPermGens);
      Add(TargetListMatrGens, eMat);
    fi;
  end;
  for eElt in TheGRPperm
  do
    eMat:=FindTransformation(eSystTotal, eSystTotal, eElt);
    if FuncTestBelong(eMat)=true then
      FuncInsert(eElt, eMat);
    fi;
  od;
  TargetMatrGrp:=PersoGroupMatrix(TargetListMatrGens, n);
  SetSize(TargetMatrGrp, Order(TargetPermGrp));
  return rec(BigMatrGrp:=TheGRPmatr, BigPermGrp:=TheGRPperm, 
             MatrGrp:=TargetMatrGrp, PermGrp:=TargetPermGrp);
end;


SymplecticEquivalence:=function(eSyst1, eSyst2, FuncTestBelong)
  local n, eSystTotal1, eSystTotal2, eEquiv, TheGRPperm, eElt, eProd, eMat;
  n:=Length(eSyst1[1]);
  eSystTotal1:=Concatenation(eSyst1, -eSyst1);
  eSystTotal2:=Concatenation(eSyst2, -eSyst2);
  eEquiv:=LinPolytope_Isomorphism(eSystTotal1, eSystTotal2);
  if eEquiv=false then
    return false;
  fi;
  TheGRPperm:=LinPolytope_Automorphism(eSystTotal1);
  for eElt in TheGRPperm
  do
    eProd:=eElt*eEquiv;
    eMat:=FindTransformation(eSystTotal1, eSystTotal2, eProd);
    if FuncTestBelong(eMat)=true then
      return rec(eElt:=eProd, eMat:=eMat);
    fi;
  od;
  return false;
end;









# eFace1 has less elements than eFace2
# we return all matrices M in the group such that
# eFace1*M is included in eFace2
ListEmbedding:=function(eFace1, eFace2, FuncTestBelong)
  local eFace1tot, eFace2tot, nb2tot, eFace1red, eMatInv, TheDim, ListSolutions, eSet, eFace2sel, eMat, relSet, eFace2totSet, pos, ListSets, ePerm, pSet;
  TheDim:=Length(eFace1[1]);
  eFace1tot:=Concatenation(eFace1, -eFace1);
  eFace2tot:=Concatenation(eFace2, -eFace2);
  eFace2totSet:=Set(eFace2tot);
  nb2tot:=Length(eFace2tot);
  eFace1red:=RowReduction(eFace1).EXT;
  eMatInv:=Inverse(eFace1red);
  ListSolutions:=[];
  ListSets:=[];
  for pSet in Combinations([1..nb2tot],TheDim)
  do
    if RankMat(eFace2tot{pSet})=TheDim then
      for ePerm in SymmetricGroup(TheDim)
      do
        eSet:=Permuted(pSet, ePerm);
        eFace2sel:=eFace2tot{eSet};
        eMat:=eMatInv*eFace2sel;
        if FuncTestBelong(eMat) then
          relSet:=Set(List(eFace1tot*eMat, x->Position(eFace2totSet, x)));
          pos:=Position(relSet, fail);
          if pos=fail then
            if Position(ListSets, relSet)=fail then
              Add(ListSolutions, eMat);
              Add(ListSets, relSet);
            fi;
          fi;
        fi;
      od;
    fi;
  od;
  return rec(ListSolutions:=ListSolutions, ListSets:=ListSets);
end;


# We find all matrices M in the group such that
# eFace1 is included in eFace2*M
ListEmbeddingRev:=function(eFace1, eFace2, FuncTestBelong)
  local eRec, eFace1tot, eFace2tot, ListMat, ListSets, eImg, eMat;
  eFace1tot:=Set(Concatenation(eFace1, -eFace1));
  eFace2tot:=Set(Concatenation(eFace2, -eFace2));
  eRec:=ListEmbedding(eFace1, eFace2, FuncTestBelong);
  ListSets:=[];
  ListMat:=[];
  for eMat in eRec.ListSolutions
  do
    eImg:=Set(eFace2tot*Inverse(eMat));
    if Position(ListSets, eImg)=fail then
      Add(ListSets, eImg);
      Add(ListMat, Inverse(eMat));
    fi;
  od;
  return ListMat;
end;







# Now we do it orbitwise...
ListEmbeddingRevTotal:=function(eFace1, eFace2, FuncTestBelong)
  local eStab, ListSolution, ListCandidates, ListStatus, nbCase, eMat, eSyst, eSystTot, TheAction, ListMat, iCase, eRec, nbEnt, iEnt, pos, eFace1tot;
  eStab:=SymplecticStabilizer(eFace1, FuncTestBelong).MatrGrp;
  eFace1tot:=Set(Concatenation(eFace1, -eFace1));
  ListSolution:=ListEmbeddingRev(eFace1, eFace2, FuncTestBelong);
  ListCandidates:=[];
  ListStatus:=[];
  nbCase:=Length(ListSolution);
  for eMat in ListSolution
  do
    eSyst:=eFace2*eMat;
    eSystTot:=Set(Concatenation(eSyst, -eSyst));
    if IsSubset(eSystTot, eFace1tot)=false then
      Error("Please debug from here 1");
    fi;
    Add(ListCandidates, eSystTot);
    Add(ListStatus, 1);
  od;
  TheAction:=function(x,g)
    return Set(x*g);
  end;
  ListMat:=[];
  for iCase in [1..nbCase]
  do
    if ListStatus[iCase]=1 then
      eRec:=OrbitWithAction(eStab, ListCandidates[iCase], TheAction);
      nbEnt:=Length(eRec.ListCoset);
      for iEnt in [1..nbEnt]
      do
        if IsSubset(eRec.ListCoset[iEnt], eFace1tot)=false then
          Error("Please debug from here 2");
        fi;
        pos:=Position(ListCandidates, eRec.ListCoset[iEnt]);
        if pos<>fail then
          ListStatus[pos]:=0;
        fi;
        Add(ListMat, ListSolution[iCase]*eRec.ListElement[iEnt]);
      od;
    fi;
  od;
  return ListMat;
end;




GetComplexListSystems:=function(ListListFaces, FuncTestBelong)
  local n, TheDim, ListOrbitByRank, i, FuncSignatureDet, ListRecord, ListIFace, ListSign, ListElt, TheBoundary, ListOccuringCoefficients, eAddElt, pos, eRecStab, jFace, eRec, eMulSign, eCharSystTot, ListElementM2, ListSystemsM2, eSign, iFaceM2, eEltM2, iFaceBound, eSignM2, eBound, sizBound, nbFace, eCharSyst, eElt, eMat, iFace, nbOrbSmall, iSubFace, nbOrb, eFace, iOrb, eFace1, ListSolutions, eSyst, eSystTot, ListContained, eRecSol, ListSystemsM1, eFaceTot, GetResolution, OneFace, eRotSubgroup, TheStab, ListSignGens, ListMatrGens, TheSym2, ePerm, nbOrbit, iRank, TheRank, eGen, iOrbit;
  OneFace:=ListListFaces[1][1];
  n:=Length(OneFace[1]);
  TheDim:=Length(ListListFaces);
  ListOrbitByRank:=[];
  Add(ListOrbitByRank, [rec(eFace:=[], BoundaryImage:="irrelevant")]);
  FuncSignatureDet:=function(iRank, iFace, eElt)
    local TheRec, iFaceLow, eEltLow, eSignLow, eSyst, eSystTot, iBound, iFaceSec, eEltSec, eSignSec, eSystSec, eSystTotSec, eEltPres, eSystChosen, eSystChosenTot, eProd, ListContained;
    if iRank=0 then
      return 1;
    fi;
    TheRec:=ListOrbitByRank[iRank+2][iFace];
    if not(eElt in TheRec.TheStab) then
      Print("The Element does not stabilize\n");
      Print("It cannot work\n");
      Error("Please correct");
    fi;
    iFaceLow:=TheRec.BoundaryImage.ListIFace[1];
    eSignLow:=TheRec.BoundaryImage.ListSign[1];
    eEltLow:=TheRec.BoundaryImage.ListElt[1];
    eProd:=eEltLow*eElt;
    eSystChosen:=ListListFaces[iRank][iFaceLow]*eEltLow;
    eSystChosenTot:=Set(Concatenation(eSystChosen, -eSystChosen));
    eSyst:=ListListFaces[iRank][iFaceLow]*eProd;
    eSystTot:=Set(Concatenation(eSyst, -eSyst));
    ListContained:=[];
    for iBound in [1..Length(TheRec.BoundaryImage.ListIFace)]
    do
      iFaceSec:=TheRec.BoundaryImage.ListIFace[iBound];
      eEltSec:=TheRec.BoundaryImage.ListElt[iBound];
      eSystSec:=ListListFaces[iRank][iFaceSec]*eEltSec;
      eSystTotSec:=Set(Concatenation(eSystSec, -eSystSec));
      Add(ListContained, eSystTotSec);
    od;
    for iBound in [1..Length(TheRec.BoundaryImage.ListIFace)]
    do
      iFaceSec:=TheRec.BoundaryImage.ListIFace[iBound];
      if iFaceSec=iFaceLow then
        eEltSec:=TheRec.BoundaryImage.ListElt[iBound];
        eSignSec:=TheRec.BoundaryImage.ListSign[iBound];
        eSystSec:=ListListFaces[iRank][iFaceSec]*eEltSec;
        eSystTotSec:=Set(Concatenation(eSystSec, -eSystSec));
        if eSystTotSec=eSystTot then
          eEltPres:=eEltLow*eElt*(eEltSec^(-1));
          return eSignSec*eSignLow*FuncSignatureDet(iRank-1, iFaceLow, eEltPres);
        fi;
      fi;
    od;
    Error("We should never reach that stage BUG");
  end;
  for i in [1..TheDim]
  do
    Print("i=", i, "\n");
    ListRecord:=[];
    nbOrb:=Length(ListListFaces[i]);
    for iOrb in [1..nbOrb]
    do
      eFace:=ListListFaces[i][iOrb];
      eFaceTot:=Set(Concatenation(eFace, -eFace));
      eRecStab:=SymplecticStabilizer(eFace, FuncTestBelong);
      if i=1 then
        TheBoundary:=rec(ListIFace:=[1], ListSign:=[1], ListElt:=[IdentityMat(n)]);
      else
        nbOrbSmall:=Length(ListListFaces[i-1]);
        ListIFace:=[];
        ListElt:=[];
        for iSubFace in [1..nbOrbSmall]
        do
          eFace1:=ListListFaces[i-1][iSubFace];
          ListSolutions:=ListEmbeddingRevTotal(eFace, eFace1, FuncTestBelong);
          for eMat in ListSolutions
          do
            Add(ListIFace, iSubFace);
            Add(ListElt, eMat);
          od;
        od;
        nbFace:=Length(ListElt);
        if i=2 then
          if nbFace<>2 then
            Error("Deep inconsistency at level 1");
          fi;
          ListSign:=[1,-1];
        else
          ListSystemsM2:=[];
          ListSystemsM1:=[];
          ListElementM2:=[];
          ListOccuringCoefficients:=[];
          for iFace in [1..nbFace]
          do
            jFace:=ListIFace[iFace];
            eElt:=ListElt[iFace];
            eBound:=ListOrbitByRank[i][jFace].BoundaryImage;
            sizBound:=Length(eBound.ListElt);
            eSyst:=eFace1*Inverse(eMat);
            eSystTot:=Set(Concatenation(eSyst, -eSyst));
            Add(ListSystemsM1, eSystTot);
            for iFaceBound in [1..sizBound]
            do
              eEltM2:=eBound.ListElt[iFaceBound];
              eSignM2:=eBound.ListSign[iFaceBound];
              iFaceM2:=eBound.ListIFace[iFaceBound];
              eAddElt:=eEltM2*eElt;
              eCharSyst:=ListListFaces[i-2][iFaceM2]*eAddElt;
              eCharSystTot:=Set(Concatenation(eCharSyst, -eCharSyst));
              pos:=Position(ListSystemsM2, eCharSystTot);
              if pos=fail then
                Add(ListSystemsM2, eCharSystTot);
                Add(ListElementM2, eAddElt);
                Add(ListOccuringCoefficients, [rec(Sign:=eSignM2, idx:=iFace)]);
              else
                eMulSign:=FuncSignatureDet(i-3, iFaceM2, ListElementM2[pos]*eAddElt^(-1));
                Add(ListOccuringCoefficients[pos], rec(Sign:=eMulSign*eSignM2, idx:=iFace));
              fi;
            od;
          od;
          ListSign:=UntangleAllSigns(ListOccuringCoefficients, nbFace);
        fi;
        TheBoundary:=rec(ListIFace:=ListIFace, ListElt:=ListElt, ListSign:=ListSign);
      fi;
      eRec:=rec(TheStab:=eRecStab.MatrGrp, BoundaryImage:=TheBoundary);
      Add(ListRecord, eRec);
    od;
    Add(ListOrbitByRank, ListRecord);
  od;
  TheRank:=Length(ListOrbitByRank)-2;
  for iRank in [0..TheRank]
  do
    nbOrbit:=Length(ListOrbitByRank[iRank+2]);
    for iOrbit in [1..nbOrbit]
    do
      TheStab:=ListOrbitByRank[iRank+2][iOrbit].TheStab;
      ListMatrGens:=GeneratorsOfGroup(TheStab);
      TheSym2:=SymmetricGroup(2);
      ListSignGens:=[];
      for eGen in ListMatrGens
      do
        eSign:=FuncSignatureDet(iRank, iOrbit, eGen);
        if eSign=1 then
          ePerm:=();
        else
          ePerm:=(1,2);
        fi;
        Add(ListSignGens, ePerm);
      od;
      eRotSubgroup:=GetKernelOfMapping(TheStab, TheSym2, ListMatrGens, ListSignGens);
      ListOrbitByRank[iRank+2][iOrbit].RotationSubgroup:=eRotSubgroup;
    od;
  od;
  GetResolution:=function(GRP, kLevel)
    return ResolutionComingFromHAP(GRP, kLevel);
  end;
  return rec(GetResolution:=GetResolution, 
             IdentityElt:=IdentityMat(n), 
             ListOrbitByRank:=ListOrbitByRank);
end;




SP4Z_GetList_Faces:=function()
  local eFace4, eFace3_1, eFace3_2, eFace3_3, eFace2_1, eFace2_2, eFace2_3, eFace1_1, eFace1_2, eFace0_1, eFace0_2, ListListFaces;
  eFace4:=IdentityMat(4);

  eFace3_1:=Concatenation(IdentityMat(4), [[1,0,0,1]]);
  eFace3_2:=Concatenation(IdentityMat(4), [[1,0,1,0],[0,1,0,1]]);
  eFace3_3:=Concatenation(IdentityMat(4), 
  [[1,1,0,0],[0,1,0,1],[1,0,1,-1]]);

  eFace2_1:=Concatenation(IdentityMat(4), 
  [[1,0,0,1],[0,1,1,0]]);
  eFace2_2:=Concatenation(IdentityMat(4), 
  [[1,1,0,0],[1,0,0,-1],[0,1,0,1],[1,0,1,-1]]);
  eFace2_3:=Concatenation(IdentityMat(4),
  [[1,1,0,0],[1,0,1,0],[0,1,0,1],[1,0,1,-1]]);

  eFace1_1:=Concatenation(IdentityMat(4), 
  [[1,1,0,0],[1,0,1,0],[1,0,0,-1],[0,1,0,1],[1,0,1,-1]]);
  eFace1_2:=Concatenation(IdentityMat(4), 
  [[1,1,0,0],[0,1,0,-1],[0,0,1,-1],[1,1,-1,0],[1,0,-1,1]]);

  eFace0_1:=Concatenation(IdentityMat(4), 
  [[1,1,0,0],[1,0,1,0],[1,0,0,-1],[0,1,0,1],[1,1,1,0],[1,0,1,-1]]);
  eFace0_2:=Concatenation(IdentityMat(4), 
  [[1,1,0,0],[1,0,-1,0],[0,1,0,-1],[0,0,1,-1],[1,1,-1,0],[1,1,0,-1],[1,0,-1,1],[0,1,1,-1]]);

  ListListFaces:=[
  [eFace0_1,eFace0_2],
  [eFace1_1,eFace1_2],
  [eFace2_1,eFace2_2,eFace2_3],
  [eFace3_1,eFace3_2,eFace3_3],
  [eFace4]];
  return ListListFaces;
end;

SP4Z_GetFlippingInfo_V1:=function(RecSP4Z)
  local ListListFacesCoho, GetTotality, GetGRPconf, GetEquivConf, len, nbPerf, nbRidge, ListSHVperf, ListSHVridge, ListSHVperfTot, ListSHVridgeTot, ListGram, ListSHVgroup, ListListVect, ListListSets, ListGRPperf, ListGRPridge, GetEquivPerf, GetEquivRidge, eReply, ListArray, ListArrayEquiv, eSet, GramFlip, eSHVridge, eRecRidge, iPerf, eSHVgroup;
  ListListFacesCoho:=RecSP4Z.ListListFacesCoho;
  GetTotality:=function(SHV)
    return Set(Concatenation(SHV, -SHV));
  end;
  GetGRPconf:=function(SHV)
    local SHVtot, PermGRP, ListMatrGen, ePerm, eMat;
    SHVtot:=GetTotality(SHV);
    PermGRP:=LinPolytope_Automorphism(SHVtot);
    ListMatrGen:=[];
    for ePerm in GeneratorsOfGroup(PermGRP)
    do
      eMat:=FindTransformation(SHVtot, SHVtot, ePerm);
      Add(ListMatrGen, eMat);
    od;
    return Group(ListMatrGen);
  end;
  GetEquivConf:=function(SHV1, SHV2)
    local SHVtot1, SHVtot2, eEquiv, eMat;
    SHVtot1:=GetTotality(SHV1);
    SHVtot2:=GetTotality(SHV2);
    eEquiv:=LinPolytope_Isomorphism(SHVtot1, SHVtot2);
    if eEquiv=false then
      return false;
    fi;
    eMat:=FindTransformation(SHVtot1, SHVtot2, eEquiv);
    return eMat;
  end;
  len:=Length(ListListFacesCoho);
  nbPerf:=Length(ListListFacesCoho[len]);
  nbRidge:=Length(ListListFacesCoho[len-1]);
  ListSHVperf:=List(ListListFacesCoho[len], x->x);
  ListSHVridge:=List(ListListFacesCoho[len-1], x->x);
  ListSHVperfTot:=List(ListSHVperf, GetTotality);
  ListSHVridgeTot:=List(ListSHVridge, GetTotality);
  ListSHVgroup:=List(ListSHVperf, y->List(y, x->[x,-x]));
  ListListVect:=List(ListSHVperf, y->List(y, x->SymmetricMatrixToVector(TransposedMat([x])*[x])));
  ListListSets:=List(ListListVect, DualDescriptionSets);
  ListGRPperf:=List(ListSHVperf, GetGRPconf);
  ListGRPridge:=List(ListSHVridge, GetGRPconf);
  GetEquivPerf:=function(TheGram)
    local eSHV, jPerf, eEquiv, eMat, eProd;
    eSHV:=ShortestVectorDutourVersion(TheGram);
    for jPerf in [1..nbPerf]
    do
      eEquiv:=ArithmeticIsomorphism([ListGram[jPerf]], [TheGram]);
      if eEquiv<>false then
        for eMat in ListGRPperf[jPerf]
        do
          eProd:=eMat*Inverse(eEquiv);
          if Set(ListSHVperfTot[jPerf]*eProd)<>Set(eSHV) then
            Error("Matrix error, please rework");
          fi;
          if RecSP4Z.FuncTestBelong(eProd) then
            return rec(iPerf:=jPerf, eEquiv:=eProd);
          fi;
        od;
        return fail;
      fi;
    od;
    Error("We should not reach that stage");
  end;
  GetEquivRidge:=function(eSHVridge)
    local eSHVtot, iRidge, eEquiv, eMat, eProd;
    eSHVtot:=GetTotality(eSHVridge);
    for iRidge in [1..nbRidge]
    do
      eEquiv:=GetEquivConf(ListSHVridge[iRidge], eSHVridge);
      if eEquiv<>false then
        for eMat in ListGRPridge[iRidge]
        do
          eProd:=eMat*eEquiv;
          if Set(ListSHVridgeTot[iRidge]*eProd)<>eSHVtot then
            Error("Error in GetRidgeRepresentation");
          fi;
          if RecSP4Z.FuncTestBelong(eProd) then
            return rec(iRidge:=iRidge, eEquivRidge:=eProd);
          fi;
        od;
      fi;
    od;
    return fail;
  end;
  ListArray:=[];
  for iPerf in [1..nbPerf]
  do
    ListArrayEquiv:=[];
    eSHVgroup:=ListSHVgroup[iPerf];
    for eSet in ListListSets[iPerf]
    do
      GramFlip:=DoFlipping_perfectform(eSHVgroup, eSet);
      eReply:=GetEquivPerf(GramFlip);
      if eReply<>fail then
        eSHVridge:=ListSHVperf[iPerf]{eSet};
        eRecRidge:=GetEquivRidge(eSHVridge);
        if eRecRidge<>fail then
          eReply.iRidge:=eRecRidge.iRidge;
          eReply.eEquivRidge:=eRecRidge.eEquivRidge;
          Add(ListArrayEquiv, eReply);
        fi;
      fi;
    od;
    Add(ListArray, ListArrayEquiv);
  od;
  return rec(ListArray:=ListArray);
end;






SP4Z_GetList_Faces_Coho:=function()
  local eFace6_1, eFace5_1, eFace4_1, eFace4_2, eFace3_1, eFace3_2, eFace3_3, eFace2_1, eFace2_2, eFace2_3, eFace1_1, eFace1_2, eFace0_1, eFace0_2, ListListFaces, eInvMat, FuncTestBelong1, FuncTestBelong2, ListListFacesCoho, ListListFacesCohoB, ePerm, Pmat, i, j, fInvMat;
  ListListFaces:=SP4Z_GetList_Faces();
  eFace0_1:=ListListFaces[1][1];
  eFace0_2:=ListListFaces[1][2];
  eFace1_1:=ListListFaces[2][1];
  eFace1_2:=ListListFaces[2][2];
  eFace2_1:=ListListFaces[3][1];
  eFace2_2:=ListListFaces[3][2];
  eFace2_3:=ListListFaces[3][3];
  eFace3_1:=ListListFaces[4][1];
  eFace3_2:=ListListFaces[4][2];
  eFace3_3:=ListListFaces[4][3];
  eFace4_1:=ListListFaces[5][1];
  eFace4_2:=[[1,0,0,0],[0,1,0,0],[1,1,0,0]];
  eFace5_1:=[[1,0,0,0],[0,1,0,0]];
  eFace6_1:=[[1,0,0,0]];
  ListListFacesCoho:=[
    [eFace6_1],
    [eFace5_1],
    [eFace4_1,eFace4_2],
    [eFace3_1,eFace3_2,eFace3_3],
    [eFace2_1,eFace2_2,eFace2_3],
    [eFace1_1,eFace1_2],
    [eFace0_1,eFace0_2]];
  eInvMat:=[
[0 ,0 ,0 ,1],
[0 ,0 ,1 ,0],
[0 ,-1,0 ,0],
[-1, 0,0 ,0]];
  ePerm:=(1,2);
  Pmat:=NullMat(4,4);
  for i in [1..4]
  do
    j:=OnPoints(i, ePerm);
    Pmat[i][j]:=1;
  od;
  fInvMat:=Pmat*eInvMat*TransposedMat(Pmat);
  ListListFacesCohoB:=List(ListListFacesCoho, x->List(x, y->y*Inverse(Pmat)));
  return rec(ListListFacesCoho:=ListListFacesCohoB,
             eInvMat:=fInvMat);
end;


# This is the method for covering the case
# of eFace2 full-dimensional and
# eFace1 not necessarily full dimensional
# The FuncTestBelong typically is about to test whether elements
# belong to the symplectic group Sp(4,Z).
SP4Z_GetAllEmbeddings:=function(eFace1, eFace2, FuncTestBelong)
  local eFace1span, eFace1tot, eFace2tot, FindEmbedding, ListMat, eSet, test, len, ListSet, ListMatRet, eSetSet;
  if RankMat(eFace1)=4 then
    return ListEmbedding(eFace1, eFace2, FuncTestBelong).ListSolutions;
  fi;
  if SYMPL_IsLagrangianSubspace(eFace1)=false then
    Error("We need to build another method");
  fi;
  eFace1span:=RowReduction(eFace1).EXT;
  eFace1tot:=Set(Concatenation(eFace1, -eFace1));
  eFace2tot:=Set(Concatenation(eFace2, -eFace2));
  len:=Length(eFace1span);
  FindEmbedding:=function(eSet)
    local eVect, eFace2img, i, RetMat;
    for eVect in BuildSet(len, [-1,1])
    do
      eFace2img:=[];
      for i in [1..len]
      do
        Add(eFace2img, eVect[i]*eFace2[eSet[i]]);
      od;
      RetMat:=SYMPL_LagrangianEquivalence(eFace1span, eFace2img);
      if IsSubset(eFace2tot, eFace1tot*RetMat) then
        return RetMat;
      fi;
    od;
    return fail;
  end;
  ListMat:=[];
  ListSet:=[];
  for eSet in Combinations([1..Length(eFace2)], len)
  do
    if RankMat(eFace2{eSet})=len and SYMPL_IsLagrangianSubspace(eFace2{eSet}) then
      test:=FindEmbedding(eSet);
      if test<>fail then
        eSet:=Set(List(eFace1*test, x->GetPositionAntipodal(eFace2, x)));
        if Position(eSet, fail)<>fail then
          Error("Clear error in Lagrangian business");
        fi;
        Add(ListMat, test);
        Add(ListSet, eSet);
      fi;
    fi;
  od;
  eSetSet:=Set(ListSet);
  ListMatRet:=List(eSetSet, x->ListMat[Position(ListSet, x)]);
  return ListMatRet;
end;


TotSet:=function(EXT)
  return Set(Concatenation(EXT, -EXT));
end;

TestEquality:=function(eConf1, eConf2)
  local eConfTot1, eConfTot2;
  eConfTot1:=Set(Concatenation(eConf1, -eConf1));
  eConfTot2:=Set(Concatenation(eConf2, -eConf2));
  return eConfTot1=eConfTot2;
end;

SP4Z_GetFlippingInfo:=function(RecSP4Z, FuncTestBelong)
  local ListListFacesCoho, len, nbPerf, nbRidge, ListListAdj, ePerf, ListAdj, iRidge, eRidge, ListMat, eMat, eFace1, ListCont, jPerf, ListMatB, eMatB, eFace2, eRec, ListSide, eSide, fPerf, eAdj, iPerf, iMat, nbMat, eSet, hMat;
  ListListFacesCoho:=RecSP4Z.ListListFacesCoho;
  len:=Length(ListListFacesCoho);
  nbPerf:=Length(ListListFacesCoho[len]);
  nbRidge:=Length(ListListFacesCoho[len-1]);
  ListListAdj:=[];
  for iPerf in [1..nbPerf]
  do
    ePerf:=ListListFacesCoho[len][iPerf];
    Print("iPerf=", iPerf, "/", nbPerf, "\n");
    ListAdj:=[];
    for iRidge in [1..nbRidge]
    do
      eRidge:=ListListFacesCoho[len-1][iRidge];
      ListMat:=ListEmbedding(eRidge, ePerf, FuncTestBelong).ListSolutions;
      nbMat:=Length(ListMat);
      Print("iRidge=", iRidge, "/", nbRidge, " |ListMat|=", nbMat, "\n");
      for iMat in [1..nbMat]
      do
        eMat:=ListMat[iMat];
        Print("iMat=", iMat, "/", nbMat, "\n");
        eFace1:=eRidge*eMat;
        eSet:=Set(List(eFace1, x->GetPositionAntipodal(ePerf, x)));
        if Position(eSet, fail)<>fail then
          Error("We have a ridge error");
        fi;
        ListCont:=[];
        for jPerf in [1..nbPerf]
        do
          fPerf:=ListListFacesCoho[len][jPerf];
          ListMatB:=ListEmbeddingRev(eFace1, fPerf, FuncTestBelong);
          for eMatB in ListMatB
          do
            eFace2:=fPerf*eMatB;
            if IsSubset(TotSet(eFace2), TotSet(eFace1))=false then
              Error("Ridge error B");
            fi;
            eRec:=rec(jPerf:=jPerf, eMatB:=eMatB, eFace2:=eFace2);
            Add(ListCont, eRec);
          od;
        od;
        if Length(ListCont)<>2 then
          Error("Inconsistency in thinness 1\n");
        fi;
        ListSide:=Filtered(ListCont, x->TestEquality(x.eFace2, ePerf)=false);
        if Length(ListSide)<>1 then
          Error("Inconsistency in thinness 2\n");
        fi;
        eSide:=ListSide[1];
        eAdj:=rec(iRidge:=iRidge, eMat:=eMat, jPerf:=eSide.jPerf, eMatB:=eSide.eMatB, eSet:=eSet);
        Add(ListAdj, eAdj);
      od;
    od;
    Add(ListListAdj, ListAdj);
  od;
  return ListListAdj;
end;


SP4Z_GetTopCells:=function(RecSP4Z, FuncTestBelong, ListListAdj, FuncGroupMembership)
  local ListListFacesCoho, len, ListStab, TestEquivalenceCells, ListTopCells, FuncInsert, nbOrbit, IsFinished, iPerf, g, eArr, ListAdj, eCell, eIns, iOrbit, eRec, eAdj, TotalListGenerators, FuncInsertTotalGen;
  ListListFacesCoho:=RecSP4Z.ListListFacesCoho;
  len:=Length(ListListFacesCoho);
  ListStab:=List(ListListFacesCoho[len], x->SymplecticStabilizer(x,FuncTestBelong).MatrGrp);
  TotalListGenerators:=[];
  TestEquivalenceCells:=function(eCell1, eCell2)
    local eMat, eQuot, EXT1, EXT2;
    if eCell1.iPerf<>eCell2.iPerf then
      return false;
    fi;
    for eMat in ListStab[eCell1.iPerf]
    do
      eQuot:=Inverse(eCell1.g)*eMat*eCell2.g;
      if FuncGroupMembership(eQuot) then
        EXT1:=ListListFacesCoho[len][eCell1.iPerf]*eCell1.g;
        EXT2:=ListListFacesCoho[len][eCell2.iPerf]*eCell2.g;
        if TotSet(EXT1*eQuot)<>TotSet(EXT2) then
          Error("Equivalence error");
        fi;
        return eQuot;
      fi;
    od;
    return false;
  end;
  ListTopCells:=[];
  FuncInsertTotalGen:=function(eMat)
    if Position(TotalListGenerators, eMat)=fail then
      Add(TotalListGenerators, eMat);
    fi;
  end;
  FuncInsert:=function(eCell)
    local iCell, fCell, test, gCell, phi, phiRed, PermGRP, PermGRPred, MatrGRP, ListPermGen, ListPermGenRed, ListMatrGen, EXT, EXTtot, FuncInsertGen, eMat, eQuot;
    for iCell in [1..Length(ListTopCells)]
    do
      fCell:=ListTopCells[iCell];
      test:=TestEquivalenceCells(fCell, eCell);
      if test<>false then
        FuncInsertTotalGen(test);
        return rec(iCell:=iCell, eEquiv:=test);
      fi;
    od;
    PermGRP:=Group(());
    PermGRPred:=Group(());
    MatrGRP:=Group([IdentityMat(4)]);
    ListPermGen:=[];
    ListPermGenRed:=[];
    ListMatrGen:=[];
    EXT:=ListListFacesCoho[len][eCell.iPerf]*eCell.g;
    EXTtot:=Concatenation(EXT, -EXT);
    FuncInsertGen:=function(eMat)
      local eList, ePerm, ePermRed, eListRed;
      eList:=List(EXTtot, x->Position(EXTtot, x*eMat));
      eListRed:=List(EXT, x->GetPositionAntipodal(EXT, x*eMat));
      ePerm:=PermList(eList);
      ePermRed:=PermList(eListRed);
      if ePerm=fail or ePermRed=fail then
        Error("The element is not correct");
      fi;
      if ePerm in ListPermGen then
        return;
      fi;
      Add(ListPermGen, ePerm);
      Add(ListPermGenRed, ePermRed);
      Add(ListMatrGen, eMat);
      PermGRP:=Group(ListPermGen);
      PermGRPred:=Group(ListPermGenRed);
      MatrGRP:=Group(ListMatrGen);
      FuncInsertTotalGen(eMat);
    end;
    for eMat in ListStab[eCell.iPerf]
    do
      eQuot:=Inverse(eCell.g)*eMat*eCell.g;
      if FuncGroupMembership(eQuot) then
        FuncInsertGen(eQuot);
      fi;
    od;
    phi:=GroupHomomorphismByImagesNC(PermGRP, MatrGRP, ListPermGen, ListMatrGen);
    gCell:=rec(iPerf:=eCell.iPerf, g:=eCell.g, TheStab:=MatrGRP, phi:=phi, PermGRP:=PermGRP, PermGRPred:=PermGRPred, EXT:=EXT, Status:="NO");
    Add(ListTopCells, gCell);
    return rec(iCell:=Length(ListTopCells), eEquiv:=IdentityMat(4));
  end;
  eCell:=rec(iPerf:=1, g:=IdentityMat(4));
  FuncInsert(eCell);
  while(true)
  do
    nbOrbit:=Length(ListTopCells);
    IsFinished:=true;
    for iOrbit in [1..nbOrbit]
    do
      if ListTopCells[iOrbit].Status="NO" then
        ListTopCells[iOrbit].Status:="YES";
        IsFinished:=false;
        iPerf:=ListTopCells[iOrbit].iPerf;
        g:=ListTopCells[iOrbit].g;
        ListAdj:=[];
        for eAdj in ListListAdj[iPerf]
        do
          eCell:=rec(iPerf:=eAdj.jPerf, g:=eAdj.eMatB*g);
          eIns:=FuncInsert(eCell);
          eIns.eSet:=eAdj.eSet;
          if IsSubset(TotSet(ListTopCells[eIns.iCell].EXT*eIns.eEquiv), TotSet(ListTopCells[iOrbit].EXT{eAdj.eSet}))=false then
            Error("Inclusion error");
          fi;
          Add(ListAdj, eIns);
        od;
        ListTopCells[iOrbit].ListAdj:=ListAdj;
      fi;
    od;
    if IsFinished then
      break;
    fi;
  od;
  return rec(ListTopCells:=ListTopCells,
             TotalListGenerators:=TotalListGenerators);
end;


SP4Z_TestEquivalenceTriple:=function(ListTopCells, eTriple1, eTriple2)
  local test, testMatr, EXT, EXTtot, EXT1tot, EXT2tot, eSet1Tot, eSet2Tot, testB, eMatRet, EXT1, EXT2;
  if eTriple1.iTopCell<>eTriple2.iTopCell then
    return false;
  fi;
  test:=RepresentativeAction(ListTopCells[eTriple1.iTopCell].PermGRPred, eTriple1.eSet, eTriple2.eSet, OnSets);
  if test=fail then
    return false;
  fi;
  EXT:=ListTopCells[eTriple1.iTopCell].EXT;
  EXTtot:=Concatenation(EXT, -EXT);
  EXT1tot:=Concatenation(EXT{eTriple1.eSet}, -EXT{eTriple1.eSet});
  EXT2tot:=Concatenation(EXT{eTriple2.eSet}, -EXT{eTriple2.eSet});
  eSet1Tot:=Set(List(EXT1tot, x->Position(EXTtot, x)));
  eSet2Tot:=Set(List(EXT2tot, x->Position(EXTtot, x)));
  testB:=RepresentativeAction(ListTopCells[eTriple1.iTopCell].PermGRP, eSet1Tot, eSet2Tot, OnSets);
  testMatr:=Image(ListTopCells[eTriple1.iTopCell].phi, testB);
  eMatRet:=Inverse(eTriple1.eMat)*testMatr*eTriple2.eMat;
  EXT1:=ListTopCells[eTriple1.iTopCell].EXT{eTriple1.eSet}*eTriple1.eMat;
  EXT2:=ListTopCells[eTriple2.iTopCell].EXT{eTriple2.eSet}*eTriple2.eMat;
  if TotSet(EXT1*eMatRet)<>TotSet(EXT2) then
    Error("Error in SP4Z_TestEquivalenceTriple");
  fi;
  return eMatRet;
end;


#
# The function below computes the boundary operators by the classical
# sign method without considering the orbits.
# In this technique, we need also the faces at infinity.
# For the computation of the orbits in infinity case, we need
# algorithm that splits the orbits.
# The ListTopCells contains all the information about the orbits.
#
# The thing is: we cannot use orbit splitting for the lower dimensional
# cells because to do pure group theoretic orbit splitting in the lower
# dimensional cells is equivalence to do double coset decomposition.
# And we know that the naive algorithm for double coset decomposition
# does not work.
# Thus we need the Voronoi algorithm for top dimensional OR list of
# cosets for the finite index subgroup.
#
SP4Z_GetCellComplex:=function(RecSP4Z, FuncTestBelong, ListArray, ListTopCells, FuncGroupMembership, EliminateInfinity, LevelSearch)
  local ListListFacesCoho, len, SaturationAndStabilizer, nbPerf, nbTopCells, LLLL_Embed, LLL_Embed, ListListEmbed, ListRec, nbOrbit, iOrbit, eFace1, iPerf, ePerf, ListMat, eSet, eRec, FuncInsertOrbit, eTopCell, iTopCell, jTopCell, eAdjInfo, i, eMat, TotalListOrbit, ListOrbit, eTriple, g, iPerfect, LLL_Index, LL_Index, L_Index, eInfo, EXT, nbOrbitB, iOrbitB, ListSign, ListSetM1, ListSetM2, iFaceM1, ListEltM2, iRec, iFace, ListElt, ListIFace, eSetM1, len2, iFaceM2, eAddElt, TheBoundary, EXTfaceM2, pos, iDim, eQuad, idx, eEltM1, EXTfaceM1, EXTimg, eList, eMulSign, TheSym2, eElt1, eGen, eSignPerm, ePerm, i2, eSignM2, eEltM2, SetImg, ListOccuringCoefficients, ListMatrGens, iFace1, eSet1, eSign1, ListFacesM2, eQuot, ListPermGen, EXTspec, eSignTot, PermGrpOr, EXT1, eSet1Img, eSign, ListSignGens, PermGrp, eOrbit, PermGRPsing, uMat, EXTface, lenIFace;
  ListListFacesCoho:=RecSP4Z.ListListFacesCoho;
  len:=Length(ListListFacesCoho);
  #
  # The triple business.
  #
  SaturationAndStabilizer:=function(eTriple)
    local ListGenStab, ListTriple, ListStatus, FuncInsertTriple, nbTriple, IsFinished, iTriple, eSet, fSet, eMat, fMat, eMatF, EXTimg, fTriple, eBasis, FuncInsertMatrGen, TheStab, eGen, eGenMatr, TheStabB, EXT, EXTtot, eSetTot, EXTcell, NewTriple, iTopCell, NewGen;
    ListGenStab:=[];
    ListTriple:=[];
    ListStatus:=[];
    EXT:=ListTopCells[eTriple.iTopCell].EXT{eTriple.eSet}*eTriple.eMat;
    EXTcell:=ListTopCells[eTriple.iTopCell].EXT;
    EXTtot:=Concatenation(EXTcell, -EXTcell);
    FuncInsertMatrGen:=function(eMat)
      local eList, ePerm;
      if First(EXT, x->GetPositionAntipodal(EXT, x*eMat)=fail)<>fail then
        Error("Clearly the generator is wrong");
      fi;
      if Position(ListGenStab, eMat)=fail then
        Add(ListGenStab, eMat);
      fi;
#      eList:=List(EXT, x->GetPositionAntipodal(EXT, x*eMat));
#      ePerm:=PermList(eList);
#      Print("ePerm=", ePerm, "\n");
    end;
    eSetTot:=Set(List(Concatenation(EXTcell{eTriple.eSet}, -EXTcell{eTriple.eSet}), x->Position(EXTtot, x)));
    TheStab:=Stabilizer(ListTopCells[eTriple.iTopCell].PermGRP, eSetTot, OnSets);
    for eGen in GeneratorsOfGroup(TheStab)
    do
      eGenMatr:=Image(ListTopCells[eTriple.iTopCell].phi, eGen);
      NewGen:=Inverse(eTriple.eMat)*eGenMatr*eTriple.eMat;
      FuncInsertMatrGen(NewGen);
    od;
    FuncInsertTriple:=function(eTriple)
      local fTriple, test;
      for fTriple in ListTriple
      do
        test:=SP4Z_TestEquivalenceTriple(ListTopCells, eTriple, fTriple);
        if test<>false then
          FuncInsertMatrGen(test);
          return;
        fi;
      od;
      Add(ListTriple, eTriple);
      Add(ListStatus, 1);
    end;
    FuncInsertTriple(eTriple);
    while(true)
    do
      nbTriple:=Length(ListTriple);
      IsFinished:=true;
      for iTriple in [1..nbTriple]
      do
        if ListStatus[iTriple]=1 then
          ListStatus[iTriple]:=0;
          NewTriple:=ListTriple[iTriple];
          iTopCell:=NewTriple.iTopCell;
          eSet:=NewTriple.eSet;
          eMat:=NewTriple.eMat;
          IsFinished:=false;
          for eAdjInfo in ListTopCells[iTopCell].ListAdj
          do
            if IsSubset(eAdjInfo.eSet, eSet) then
              jTopCell:=eAdjInfo.iCell;
              fMat:=eAdjInfo.eEquiv*eMat;
              EXTimg:=ListTopCells[jTopCell].EXT*fMat;
              fSet:=Set(List(EXT, x->GetPositionAntipodal(EXTimg, x)));
              if Position(fSet, fail)<>fail then
                Error("Equivalence matrix error");
              fi;
              fTriple:=rec(iTopCell:=jTopCell, eMat:=fMat, eSet:=fSet);
              FuncInsertTriple(fTriple);
            fi;
          od;
        fi;
      od;
      if IsFinished=true then
        break;
      fi;
    od;
    TheStabB:=Group(ListGenStab);
    return rec(ListTriple:=ListTriple, TheStab:=TheStabB, EXT:=EXT);
  end;
  #
  # Preparation for enumeration of orbits. Code below is independent of the
  # finite index subgroup considered.
  #
  nbPerf:=Length(ListListFacesCoho[len]);
  nbTopCells:=Length(ListTopCells);
  LLLL_Embed:=[];
  for iDim in [1..LevelSearch]
  do
    nbOrbit:=Length(ListListFacesCoho[iDim]);
    LLL_Embed:=[];
    for iOrbit in [1..nbOrbit]
    do
      eFace1:=ListListFacesCoho[iDim][iOrbit];
      ListListEmbed:=[];
      for iPerf in [1..nbPerf]
      do
        ePerf:=ListListFacesCoho[len][iPerf];
        ListMat:=SP4Z_GetAllEmbeddings(eFace1, ePerf, FuncTestBelong);
        ListRec:=[];
        for eMat in ListMat
        do
          eSet:=Set(List(eFace1*eMat, x->GetPositionAntipodal(ePerf, x)));
          eRec:=rec(eSet:=eSet, eMat:=eMat, iPerf:=iPerf, iOrbit:=iOrbit, EXT:=eFace1*eMat);
          Add(ListRec, eRec);
        od;
        Add(ListListEmbed, ListRec);
      od;
      Add(LLL_Embed, ListListEmbed);
    od;
    Add(LLLL_Embed, LLL_Embed);
  od;
  #
  # Enumeration of orbits
  #
  TotalListOrbit:=[];
  LLL_Index:=[];
  for iDim in [1..LevelSearch]
  do
    ListOrbit:=[];
    Print("iDim=", iDim, "\n");
    FuncInsertOrbit:=function(eTriple)
      local nbOrbit, iOrbit, eOrbit, fTriple, test;
      nbOrbit:=Length(ListOrbit);
      for iOrbit in [1..nbOrbit]
      do
        eOrbit:=ListOrbit[iOrbit];
        for fTriple in eOrbit.ListTriple
        do
          test:=SP4Z_TestEquivalenceTriple(ListTopCells, fTriple, eTriple);
          if test<>false then
            return rec(iOrbit:=iOrbit, eEquiv:=test);
          fi;
        od;
      od;
      eOrbit:=SaturationAndStabilizer(eTriple);
      Add(ListOrbit, eOrbit);
      return rec(iOrbit:=Length(ListOrbit), eEquiv:=IdentityMat(4));
    end;
    nbOrbit:=Length(ListListFacesCoho[iDim]);
    LL_Index:=[];
    for iTopCell in [1..nbTopCells]
    do
      eTopCell:=ListTopCells[iTopCell];
      iPerfect:=eTopCell.iPerf;
      g:=eTopCell.g;
      L_Index:=[];
      for iOrbit in [1..nbOrbit]
      do
        for eRec in LLLL_Embed[iDim][iOrbit][iPerfect]
        do
          uMat:=IdentityMat(4);
          eTriple:=rec(eSet:=eRec.eSet, eMat:=uMat, iTopCell:=iTopCell);
          eInfo:=FuncInsertOrbit(eTriple);
          eTriple.eInfo:=eInfo;
          EXTimg:=eTopCell.EXT{eRec.eSet}*uMat;
          if IsSubset(TotSet(eTopCell.EXT), TotSet(EXTimg))=false then
            Error("EXTimg should be contained in eTopCell");
          fi;
          Add(L_Index, eTriple);
        od;
      od;
      Add(LL_Index, L_Index);
    od;
    Add(LLL_Index, LL_Index);
    Add(TotalListOrbit, ListOrbit);
    Print("   |ListOrbit|=", Length(ListOrbit), "\n");
  od;
  #
  # Now computing the boundaries
  #
  for iFace in [1..Length(TotalListOrbit[1])]
  do
    TotalListOrbit[1][iFace].BoundaryImage:=rec(PermGrp:=Group(()), PermGrpOr:=Group(()) );
  od;
  for iDim in [2..LevelSearch]
  do
    Print("Computing boundaries iDim=", iDim, "\n");
    nbOrbit:=Length(TotalListOrbit[iDim]);
    for iOrbit in [1..nbOrbit]
    do
      eOrbit:=TotalListOrbit[iDim][iOrbit];
      eTriple:=eOrbit.ListTriple[1];
      iTopCell:=eTriple.iTopCell;
      eSet:=eTriple.eSet;
      eMat:=eTriple.eMat;
      EXT:=ListTopCells[iTopCell].EXT{eSet}*eMat;
      nbOrbitB:=Length(LLL_Index[iDim-1][iTopCell]);
      ListMatrGens:=GeneratorsOfGroup(TotalListOrbit[iDim][iOrbit].TheStab);
      ListPermGen:=[];
      for eGen in ListMatrGens
      do
        eList:=List(EXT, x->GetPositionAntipodal(EXT, x*eGen));
        ePerm:=PermList(eList);
        Add(ListPermGen, ePerm);
      od;
      PermGRPsing:=Group(ListPermGen);
      ListIFace:=[];
      ListElt:=[];
      ListSetM1:=[];
      for eQuad in LLL_Index[iDim-1][iTopCell]
      do
        if IsSubset(eSet, eQuad.eSet) then
          eInfo:=eQuad.eInfo;
          Add(ListIFace, eInfo.iOrbit);
          Add(ListElt, eInfo.eEquiv);
          eSetM1:=Set(List(eQuad.eSet, x->Position(eSet, x)));
          Add(ListSetM1, eSetM1);
        fi;
      od;
      if iDim=2 then
        if Length(ListElt)<>2 then
          Error("Conceptual error on the differential");
        fi;
        ListSign:=[1,-1];
      else
        lenIFace:=Length(ListIFace);
        ListSetM2:=[];
        ListEltM2:=[];
        ListOccuringCoefficients:=[];
        for iFace in [1..lenIFace]
        do
          iFaceM1:=ListIFace[iFace];
          eEltM1:=ListElt[iFace];
          TheBoundary:=TotalListOrbit[iDim-1][iFaceM1].BoundaryImage;
          len2:=Length(TheBoundary.ListIFace);
          for i2 in [1..len2]
          do
            iFaceM2:=TheBoundary.ListIFace[i2];
            eSignM2:=TheBoundary.ListSign[i2];
            eEltM2:=TheBoundary.ListElt[i2];
            eAddElt:=eEltM2*eEltM1;
            EXTfaceM2:=TotalListOrbit[iDim-2][iFaceM2].EXT;
            EXTimg:=EXTfaceM2*eAddElt;
            SetImg:=Set(List(EXTimg, x->GetPositionAntipodal(EXT, x)));
            pos:=Position(ListSetM2, SetImg);
            if pos=fail then
              Add(ListSetM2, SetImg);
              Add(ListEltM2, eAddElt);
              Add(ListOccuringCoefficients, [rec(Sign:=eSignM2, idx:=iFace)]);
            else
              eQuot:=ListEltM2[pos]*Inverse(eAddElt);
              eList:=List(EXTfaceM2*eQuot, x->GetPositionAntipodal(EXTfaceM2, x));
              ePerm:=PermList(eList);
              if ePerm=fail then
                Error("We have a fail for permutation");
              fi;
              if not(ePerm in TotalListOrbit[iDim-2][iFaceM2].BoundaryImage.PermGrp) then
                Error("Error in building the permutation");
              fi;
              if ePerm in TotalListOrbit[iDim-2][iFaceM2].BoundaryImage.PermGrpOr then
                eMulSign:=1;
              else
                eMulSign:=-1;
              fi;
              Add(ListOccuringCoefficients[pos], rec(Sign:=eSignM2*eMulSign, idx:=iFace));
            fi;
          od;
        od;
        if First(ListOccuringCoefficients, x->Length(x)<>2)<>fail then
          Error("Please debug from here");
        fi;
        ListSign:=UntangleAllSigns(ListOccuringCoefficients, lenIFace);
      fi;
      TheSym2:=SymmetricGroup(2);
      ListPermGen:=[];
      ListSignGens:=[];
      iFace1:=ListIFace[1];
      eSet1:=ListSetM1[1];
      eSign1:=ListSign[1];
      eElt1:=ListElt[1];
      EXT1:=EXT{eSet1};
      EXTspec:=TotalListOrbit[iDim-1][iFace1].EXT;
      for eGen in ListMatrGens
      do
        eList:=List(EXT, x->GetPositionAntipodal(EXT, x*eGen));
        ePerm:=PermList(eList);
        if ePerm=fail then
          Error("fail in perm, debug 1");
        fi;
        Add(ListPermGen, ePerm);
        if iDim=2 then
          eSignPerm:=ePerm;
        else
          eSet1Img:=Set(List(EXT1*eGen, x->GetPositionAntipodal(EXT, x)));
          pos:=Position(ListSetM1, eSet1Img);
          eQuot:=eElt1*eGen*Inverse(ListElt[pos]);
          ePerm:=PermList(List(EXTspec*eQuot, x->GetPositionAntipodal(EXTspec, x)));
          if ePerm=fail then
            Error("fail in perm, debug 2");
          fi;
          if ePerm in TotalListOrbit[iDim-1][iFace1].BoundaryImage.PermGrpOr then
            eSign:=1;
          else
            eSign:=-1;
          fi;
          eSignTot:=eSign1*ListSign[pos]*eSign;
          if eSignTot=1 then
            eSignPerm:=();
          else
            eSignPerm:=(1,2);
          fi;
        fi;
        Add(ListSignGens, eSignPerm);
      od;
      PermGrp:=Group(ListPermGen);
      PermGrpOr:=GetKernelOfMapping(PermGrp, TheSym2, ListPermGen, ListSignGens);
      TheBoundary:=rec(ListIFace:=ListIFace, ListSign:=ListSign, ListElt:=ListElt, ListSetM1:=ListSetM1, PermGrp:=PermGrp, PermGrpOr:=PermGrpOr);
      TotalListOrbit[iDim][iOrbit].BoundaryImage:=TheBoundary;
    od;
  od;
  #
  #
  #
  Print("Exiting SP4Z_GetCellComplex\n");
  return rec(TotalListOrbit:=TotalListOrbit, 
             LLL_Index:=LLL_Index);
end;







# We have a double coset Gamma q Gamma
# and we split it into right cosets
# x1 Gamma , ....., xr Gamma
HECKE_DoubleCosetToRightCosets:=function(RecGroup, TheMatrix)
  local ListStatus, ListCoset, FuncInsert, nbCos, IsFinished, iCos, eProd, eGen, ProductExpression, GetStabilizerOfCoset, nbCoset, GetCosetPermutationGroup, GetKernel, GetSinglePermutation;
  ListStatus:=[];
  ListCoset:=[];
  FuncInsert:=function(eMat)
    local len, eInvMat, eCoset, eInv;
    eInvMat:=Inverse(eMat);
    for eCoset in ListCoset
    do
      eInv:=eInvMat*eCoset;
      if RecGroup.IsInGroup(eInv)=true then
        return;
      fi;
    od;
    Add(ListStatus, 0);
    Add(ListCoset, eMat);
  end;
  FuncInsert(TheMatrix);
  while(true)
  do
    nbCos:=Length(ListCoset);
    IsFinished:=true;
    for iCos in [1..nbCos]
    do
      if ListStatus[iCos]=0 then
        ListStatus[iCos]:=1;
        IsFinished:=false;
        for eGen in RecGroup.ListGen
        do
          eProd:=eGen*ListCoset[iCos];
          FuncInsert(eProd);
        od;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  nbCoset:=Length(ListCoset);
  # g in is Gamma
  # h is one coset
  # we return hp * gp
  # with hp being one coset
  #  and gp being in Gamma
  ProductExpression:=function(eProd)
    local eH, gP, iCoset;
    for iCoset in [1..nbCoset]
    do
      eH:=ListCoset[iCoset];
      gP:=Inverse(eH)*eProd;
      if eProd<>ListCoset[iCoset]*gP then
        Error("Clear error here");
      fi;
      if RecGroup.IsInGroup(gP)=true then
        return rec(hP:=eH, iCoset:=iCoset, gP:=gP);
      fi;
    od;
    Error("We should never reach that stage");
  end;
  GetStabilizerOfCoset:=function(GRP, iCoset)
    local ListGen, ListPermGens, eGen, eList, ePerm, GRPperm, RecPerm;
    ListGen:=GeneratorsOfGroup(GRP);
    ListPermGens:=List(ListGen, GetSinglePermutation);
    GRPperm:=Group(ListPermGens);
    RecPerm:=MatrixGroupPermutationRepresentation(GRP, GRPperm, Length(ListCoset), ListGen, ListPermGens);
    return RecPerm.GetStabilizerPoint(iCoset);
  end;
  GetSinglePermutation:=function(eMat)
    return PermList(List(ListCoset, x->ProductExpression(Inverse(eMat)*x).iCoset));
  end;
  GetCosetPermutationGroup:=function(GRP)
    local ListGen, ListPermGens, eGen, eList, ePerm, GRPperm;
    ListGen:=GeneratorsOfGroup(GRP);
    ListPermGens:=List(ListGen, GetSinglePermutation);
    GRPperm:=Group(ListPermGens);
    return GRPperm;
  end;
  GetKernel:=function(GRP)
    local ListGen, ListPermGens, eGen, eList, ePerm, GRPperm, RecPerm;
    ListGen:=GeneratorsOfGroup(GRP);
    ListPermGens:=List(ListGen, GetSinglePermutation);
    GRPperm:=Group(ListPermGens);
    RecPerm:=MatrixGroupPermutationRepresentation(GRP, GRPperm, Length(ListCoset), ListGen, ListPermGens);
    return RecPerm.TheKer;
  end;
  return rec(ListCoset:=ListCoset,
             ProductExpression:=ProductExpression, 
             GetKernel:=GetKernel,
             GetSinglePermutation:=GetSinglePermutation,
             GetCosetPermutationGroup:=GetCosetPermutationGroup, 
             GetStabilizerOfCoset:=GetStabilizerOfCoset);
end;


SP4Z_SequenceReduction:=function(TotalListCell)
  local nbCell, GRA, iCell, jCell, eInt, ePath;
  nbCell:=Length(TotalListCell);
  GRA:=NullGraph(Group(()), nbCell);
  for iCell in [1..nbCell-1]
  do
    for jCell in [iCell+1..nbCell]
    do
      eInt:=Intersection(TotSet(TotalListCell[iCell].EXTcell), TotSet(TotalListCell[jCell].EXTcell));
      if Length(eInt)=18 then
        AddEdgeOrbit(GRA, [iCell, jCell]);
        AddEdgeOrbit(GRA, [jCell, iCell]);
      fi;
    od;
  od;
  ePath:=FindShortestPath(GRA, 1, nbCell);
#  Print("nbCell=", nbCell, "  ePath=", ePath, "\n");
  if nbCell>1 and Length(ePath)=1 then
    Error("Path computation is broken");
  fi;
  return TotalListCell{ePath};
end;


SP4Z_GetSequenceToRay_General:=function(ListTopCells, eVect, ListContVert, eStartCell)
  local eRayVect, TotalListCell, FuncInsertECell, eInsCell, GetAdjInfoFromCell, DoFlowering, SequenceStrategy, eANS1, eANS2, nbCell, GRA, iCell, jCell, eInt, ePath, IsSubsetContained, GetCellPosition;
  eRayVect:=SymmetricMatrixToVector(TransposedMat([eVect])*[eVect]);
  TotalListCell:=[];
  IsSubsetContained:=function(eCell)
    local EXTcell;
    EXTcell:=ListTopCells[eCell.iTopCell].EXT*eCell.eMat;
    if IsSubset(TotSet(EXTcell), TotSet(ListContVert)) then
      return true;
    fi;
    return false;
  end;
  GetCellPosition:=function(eCell)
    local EXTcell, iCell, rCell;
    EXTcell:=ListTopCells[eCell.iTopCell].EXT*eCell.eMat;
    for iCell in [1..Length(TotalListCell)]
    do
      rCell:=TotalListCell[iCell];
      if TotSet(rCell.EXTcell)=TotSet(EXTcell) then
        return iCell;
      fi;
    od;
    return -1;
  end;
  FuncInsertECell:=function(eCell)
    local iTopCell, eMat, EXTcell, iCell, rCell, fCell;
    iTopCell:=eCell.iTopCell;
    eMat:=eCell.eMat;
    EXTcell:=ListTopCells[eCell.iTopCell].EXT*eCell.eMat;
    for iCell in [1..Length(TotalListCell)]
    do
      rCell:=TotalListCell[iCell];
      if TotSet(rCell.EXTcell)=TotSet(EXTcell) then
        return rec(iCell:=iCell, IsNew:=false);
      fi;
    od;
    fCell:=rec(iTopCell:=iTopCell, eMat:=eMat, EXTcell:=EXTcell);
    Add(TotalListCell, fCell);
#    Print("|TotaListCell|=", Length(TotalListCell), "\n");
    return rec(iCell:=Length(TotalListCell), IsNew:=true);
  end;
  eInsCell:=FuncInsertECell(eStartCell);
  GetAdjInfoFromCell:=function(eCell)
    local EXTcell, PerfDom, eAdjInfo, eFAC, NewCell, fMat;
    PerfDom:=List(eCell.EXTcell, x->SymmetricMatrixToVector(TransposedMat([x])*[x]));
    for eAdjInfo in ListTopCells[eCell.iTopCell].ListAdj
    do
      eFAC:=__FindFacetInequality(PerfDom, eAdjInfo.eSet);
      if eFAC*eRayVect<0 then
        fMat:=eAdjInfo.eEquiv*eCell.eMat;
        NewCell:=rec(iTopCell:=eAdjInfo.iCell, eMat:=fMat);
        if IsSubsetContained(NewCell) then
          return NewCell;
        fi;
      fi;
    od;
    return "irrelevant";
  end;
  DoFlowering:=function()
    local ListICell, ListStatus, nbCase, iCase, iCell, eCell, eAdjInfo, fMat, fCell, eRecIns, uCell, NewCell, iCellPos;
#    Print("Beginning of flowering operation\n");
    ListICell:=[Length(TotalListCell)];
    ListStatus:=[0];
    while(true)
    do
      nbCase:=Length(ListStatus);
      for iCase in [1..nbCase]
      do
        if ListStatus[iCase]=0 then
          ListStatus[iCase]:=1;
          iCell:=ListICell[iCase];
          eCell:=TotalListCell[iCell];
          for eAdjInfo in ListTopCells[eCell.iTopCell].ListAdj
          do
            fMat:=eAdjInfo.eEquiv*eCell.eMat;
            fCell:=rec(iTopCell:=eAdjInfo.iCell, eMat:=fMat);
            if IsSubsetContained(fCell) then
              eRecIns:=FuncInsertECell(fCell);
              if eRecIns.IsNew then
                uCell:=TotalListCell[eRecIns.iCell];
                if GetPositionAntipodal(uCell.EXTcell, eVect)<>fail then
#                  Print("Leaving flowering here A\n");
                  return rec(eSuccess:=true);
                fi;
                NewCell:=GetAdjInfoFromCell(uCell);
                if GetAdjInfoFromCell(uCell)<>"irrelevant" then
                  iCellPos:=GetCellPosition(NewCell);
                  if iCellPos=-1 then
#                    Print("Leaving flowering here B\n");
                    return rec(eSuccess:=false);
                  fi;
                fi;
                Add(ListICell, Length(TotalListCell));
                Add(ListStatus, 1);
              fi;
            fi;
          od;
        fi;
      od;
    od;
  end;
  SequenceStrategy:=function()
    local iter, NewCell, fMat, eCell;
    iter:=0;
    while(true)
    do
      eCell:=TotalListCell[Length(TotalListCell)];
      iter:=iter+1;
#      Print("iter=", iter, "\n");
      if GetPositionAntipodal(eCell.EXTcell, eVect)<>fail then
        return rec(eSuccess:=true);
      fi;
      NewCell:=GetAdjInfoFromCell(eCell);
#      Print("NewCell=", NewCell, "\n");
      if NewCell="irrelevant" then
        return rec(eSuccess:=false);
      fi;
      eInsCell:=FuncInsertECell(NewCell);
      if eInsCell.IsNew=false then
        Error("It should not be there already");
      fi;
    od;
  end;
  #
  #
  while(true)
  do
    eANS1:=SequenceStrategy();
    if eANS1.eSuccess then
      break;
    fi;
    eANS2:=DoFlowering();
    if eANS2.eSuccess then
      break;
    fi;
  od;
  return SP4Z_SequenceReduction(TotalListCell);
end;


SP4Z_GetSequenceToRay:=function(ListTopCells, eVect, eStartCell)
  local ListContVert;
  ListContVert:=[];
#  Print("Calling from SP4Z_GetSequenceToRay\n");
  return SP4Z_GetSequenceToRay_General(ListTopCells, eVect, ListContVert, eStartCell);
end;


SP4Z_GetSequenceToCell:=function(ListTopCells, EXTcell, eStartCell)
  local nbVert, RetSeq, iVert, ListContVert, eGoodCell, TheSeq;
  nbVert:=Length(EXTcell);
  RetSeq:=[eStartCell];
  for iVert in [1..nbVert]
  do
    ListContVert:=EXTcell{[1..iVert-1]};
    eGoodCell:=RetSeq[Length(RetSeq)];
#    Print("Calling from SP4Z_GetSequenceToCell\n");
    TheSeq:=SP4Z_GetSequenceToRay_General(ListTopCells, EXTcell[iVert], ListContVert, eGoodCell);
    Append(RetSeq, TheSeq{[2..Length(TheSeq)]});
  od;
  return SP4Z_SequenceReduction(RetSeq);
end;




SP4Z_ComputeHomologySpaces:=function(TotalListOrbit)
  local ListRecOri, iDim, nbOrbit, ListOri, iOrbit, BndImg, iOri, nbOri, ListOriRev, eRecOri, ListMat, eDim1, eDim2, eMat, i2, iOrbit2, eImg, len, TheDim, iOrbit1, TheKernel, eDim, TheSpace, TheImage, i, iFace, ListSpaces, dimKer, rnk, TheImagePre, NSP, eRecSpace;
  #
  # Determining orientable orbits
  #
  TheDim:=Length(TotalListOrbit);
  ListRecOri:=[];
  for iDim in [1..TheDim]
  do
    nbOrbit:=Length(TotalListOrbit[iDim]);
    ListOri:=[];
    for iOrbit in [1..nbOrbit]
    do
      BndImg:=TotalListOrbit[iDim][iOrbit].BoundaryImage;
      if Order(BndImg.PermGrp) = Order(BndImg.PermGrpOr) then
        Add(ListOri, iOrbit);
      fi;
    od;
    nbOri:=Length(ListOri);
    ListOriRev:=ListWithIdenticalEntries(nbOrbit,0);
    for iOri in [1..nbOri]
    do
      ListOriRev[ListOri[iOri]]:=iOri;
    od;
    eRecOri:=rec(nbOri:=nbOri, ListOri:=ListOri, ListOriRev:=ListOriRev);
    Add(ListRecOri, eRecOri);
  od;
  #
  # Computing differentials with
  # ---Killed G actions
  # ---Killed orientable faces
  #
  ListMat:=[];
  for iDim in [2..TheDim]
  do
    eDim1:=ListRecOri[iDim-1].nbOri;
    eDim2:=ListRecOri[iDim].nbOri;
    eMat:=[];
    for i2 in [1..eDim2]
    do
      iOrbit2:=ListRecOri[iDim].ListOri[i2];
      BndImg:=TotalListOrbit[iDim][iOrbit2].BoundaryImage;
      eImg:=ListWithIdenticalEntries(eDim1,0);
      len:=Length(BndImg.ListIFace);
      for i in [1..len]
      do
        iFace:=BndImg.ListIFace[i];
        iOrbit1:=ListRecOri[iDim-1].ListOriRev[iFace];
        if iOrbit1>0 then
          eImg[iOrbit1]:=eImg[iOrbit1] + BndImg.ListSign[i];
        fi;
      od;
      Add(eMat, eImg);
    od;
    Add(ListMat, eMat);
  od;
  #
  # Computing Rational Homology groups
  # We directly kill the torsion.
  # maybe later we can take care of it.
  #
  ListSpaces:=[];
  for iDim in [1..TheDim]
  do
    eDim:=ListRecOri[iDim].nbOri;
    if iDim=1 then
      TheKernel:=IdentityMat(eDim);
    else
      if eDim=0 then
        TheKernel:=[];
      else
        if Length(ListMat[iDim-1]) = 0 then
          TheKernel:=IdentityMat(eDim);
        else
          if Length(ListMat[iDim-1][1])=0 then
            TheKernel:=IdentityMat(Length(ListMat[iDim-1]));
          else
            TheKernel:=NullspaceIntMat(ListMat[iDim-1]);
          fi;
        fi;
      fi;
    fi;
    if iDim=TheDim then
      TheSpace:=TheKernel;
      TheImage:=[];
    else
      dimKer:=Length(TheKernel);
      if dimKer > 0 then
        TheImagePre:=List(ListMat[iDim], x->SolutionMat(TheKernel, x));
        if Length(TheImagePre)=0 then
          rnk:=0;
        else
          rnk:=RankMat(TheImagePre);
        fi;
        if rnk=dimKer then
          TheImage:=IdentityMat(dimKer);
          TheSpace:=[];
        else
          if rnk=0 then
            TheImage:=[];
            TheSpace:=IdentityMat(dimKer);
          else
            NSP:=NullspaceIntMat(TransposedMat(TheImagePre));
            TheImage:=NullspaceIntMat(TransposedMat(NSP));
            TheSpace:=SubspaceCompletion(TheImage, dimKer);
          fi;
        fi;
      else
        TheSpace:=[];
        TheImage:=[];
      fi;
    fi;
    eRecSpace:=rec(TheKernel:=TheKernel, TheImage:=TheImage, TheSpace:=TheSpace);
    Add(ListSpaces, eRecSpace);
  od;
  return rec(ListSpaces:=ListSpaces, ListMat:=ListMat, ListRecOri:=ListRecOri);
end;

#
# Test if the matrix is admissible for Hecke operators
# computations
SP4Z_IsInExtendedGroup:=function(eMat)
  local eInvMat, eProd, eProdRed;
  eInvMat:=SYMPL_GetSymplecticForm(2);
  eProd:=eMat*eInvMat*TransposedMat(eMat);
  eProdRed:=RemoveFractionMatrix(eProd);
  if eProdRed=eInvMat or eProdRed=-eInvMat then
    return true;
  fi;
  return false;
end;





SP4Z_ComputeImage:=function(iDim, TotalArray, TheChain)
  local TotalListOrbit, nbOrbit, nbOrbitM1, TheChainRet, FuncInsertEntry, iOrbit, BndImg, len, lenB, i, iB, iFace, eSign, eElt, eVal, eMat;
  if iDim=1 then
    Error("The rank should be greater or equal to 2");
  fi;
  TotalListOrbit:=TotalArray.CellComplex.TotalListOrbit;
  nbOrbit:=Length(TotalListOrbit[iDim]);
  nbOrbitM1:=Length(TotalListOrbit[iDim-1]);
  if Length(TheChain)<>nbOrbit then
    Error("TheChain must be of Length nbOrbit");
  fi;
  TheChainRet:=GMOD_GetZeroVector(nbOrbitM1);
  FuncInsertEntry:=function(jOrbit, eVal, eMat)
    local len, EXTcell, i, eInv, eList, ePerm, eSignOr;
    len:=Length(TheChainRet[jOrbit].ListVal);
    EXTcell:=TotalListOrbit[iDim-1][jOrbit].EXT;
    for i in [1..len]
    do
      eInv:=eMat*Inverse(TheChainRet[jOrbit].ListElt[i]);
      eList:=List(EXTcell, x->GetPositionAntipodal(EXTcell, x*eInv));
      if Position(eList, fail)=fail then
        ePerm:=PermList(eList);
        if ePerm in TotalListOrbit[iDim-1][jOrbit].BoundaryImage.PermGrpOr then
          eSignOr:=1;
        else
          eSignOr:=-1;
        fi;
        TheChainRet[jOrbit].ListVal[i]:=TheChainRet[jOrbit].ListVal[i] + eVal*eSignOr;
        return;
      fi;
    od;
    Add(TheChainRet[jOrbit].ListVal, eVal);
    Add(TheChainRet[jOrbit].ListElt, eMat);
  end;
  for iOrbit in [1..nbOrbit]
  do
    BndImg:=TotalListOrbit[iDim][iOrbit].BoundaryImage;
    len:=Length(BndImg.ListIFace);
    lenB:=Length(TheChain[iOrbit].ListVal);
    for i in [1..len]
    do
      iFace:=BndImg.ListIFace[i];
      eSign:=BndImg.ListSign[i];
      eElt:=BndImg.ListElt[i];
      for iB in [1..lenB]
      do
        eVal:=eSign*TheChain[iOrbit].ListVal[iB];
        eMat:=eElt *TheChain[iOrbit].ListElt[iB];
        FuncInsertEntry(iFace, eVal, eMat);
      od;
    od;
  od;
#  Print("TheChainRet=", TheChainRet, "\n");
  return ReducedGmoduleVector(TheChainRet);
end;




SP4Z_GetVectorFromChain:=function(iDim, TotalArray, TotalListCell, TheChain)
  local TotalNbCell, GetIndexAndSign, eVect, iOrbit, len, i, eMat, eCell, eRecIS, eVal, TotalListOrbit, nbOrbit;
  TotalListOrbit:=TotalArray.CellComplex.TotalListOrbit;
  nbOrbit:=Length(TotalListOrbit[iDim]);
  if Length(TheChain)<>nbOrbit then
    Error("TheChain must be of Length nbOrbit");
  fi;
  TotalNbCell:=Length(TotalListCell);
  GetIndexAndSign:=function(eCell)
    local iCell, fCell, eInv, eList, ePerm, BndImg, eSignOr, EXTcell;
    for iCell in [1..TotalNbCell]
    do
      fCell:=TotalListCell[iCell];
      if eCell.iOrbit=fCell.iOrbit then
        EXTcell:=TotalListOrbit[iDim][eCell.iOrbit].EXT;
        eInv:=eCell.eMat*Inverse(fCell.eMat);
        eList:=List(EXTcell, x->GetPositionAntipodal(EXTcell,x*eInv));
        if Position(eList, fail)=fail then
          ePerm:=PermList(eList);
          BndImg:=TotalListOrbit[iDim][eCell.iOrbit].BoundaryImage;
          if not(ePerm in BndImg.PermGrp) then
            Error("Belonging error to solve");
          fi;
          if ePerm in BndImg.PermGrpOr then
            eSignOr:=1;
          else
            eSignOr:=-1;
          fi;
          return rec(iCell:=iCell, eSignOr:=eSignOr);
        fi;
      fi;
    od;
    Error("Death of the unfound variety");
  end;
  eVect:=ListWithIdenticalEntries(TotalNbCell, 0);
  for iOrbit in [1..nbOrbit]
  do
    len:=Length(TheChain[iOrbit].ListVal);
    for i in [1..len]
    do
      eMat:=TheChain[iOrbit].ListElt[i];
      eCell:=rec(iOrbit:=iOrbit, eMat:=eMat);
      eRecIS:=GetIndexAndSign(eCell);
      eVal:=TheChain[iOrbit].ListVal[i]*eRecIS.eSignOr;
      eVect[eRecIS.iCell]:=eVect[eRecIS.iCell] + eVal;
    od;
  od;
  return eVect;
end;



SP4Z_TestChainEquality:=function(iDim, TotalArray, TheChain1, TheChain2)
  local TotalListOrbit, nbOrbit, TotalListCell, iOrbit, ListCell, FuncInsertCell, eG, eCell, eVect1, eVect2, EXTcell;
  if Length(TheChain1)<>Length(TheChain2) then
    Error("TheChain1 and TheChain2 must be of same Length");
  fi;
  TotalListOrbit:=TotalArray.CellComplex.TotalListOrbit;
  nbOrbit:=Length(TotalListOrbit[iDim]);
  if Length(TheChain1)<>nbOrbit then
    Error("TheChain1 must be of Length nbOrbit");
  fi;
  TotalListCell:=[];
  for iOrbit in [1..nbOrbit]
  do
    ListCell:=[];
    EXTcell:=TotalListOrbit[iDim][iOrbit].EXT;
    FuncInsertCell:=function(eCell)
      local fCell, eInv;
      for fCell in ListCell
      do
        eInv:=eCell.eMat*Inverse(fCell.eMat);
        if First(EXTcell, x->GetPositionAntipodal(EXTcell,x*eInv)=fail)=fail then
          return;
        fi;
      od;
      Add(ListCell, eCell);
    end;
    for eG in TheChain1[iOrbit].ListElt
    do
      eCell:=rec(iOrbit:=iOrbit, eMat:=eG);
      FuncInsertCell(eCell);
    od;
    for eG in TheChain2[iOrbit].ListElt
    do
      eCell:=rec(iOrbit:=iOrbit, eMat:=eG);
      FuncInsertCell(eCell);
    od;
    Append(TotalListCell, ListCell);
  od;
  #
  eVect1:=SP4Z_GetVectorFromChain(iDim, TotalArray, TotalListCell, TheChain1);
  eVect2:=SP4Z_GetVectorFromChain(iDim, TotalArray, TotalListCell, TheChain2);
  return eVect1=eVect2;
end;




SP4Z_GroupAverage:=function(iDim, TotalArray, eGRP, FuncSign, TheChain)
  local TotalListOrbit, nbOrbit, TotalListCell, iOrbit, ListCell, EXTcell, eCell, ListSign, ListGenGRP, FuncInsertCell, GetIndexAndSign, nbCell, eG, iCell, IsFinished, eMat, eGen, NewCell, TotalNbCell, eList, eSign, ListRec, FuncInsertChain, nbGen, PermGrpOr, ePerm, TotalSumVect, nbRec, iGen, NewChain, NewListVal, NewListElt, fEnt, TheAverage, TheChainRet, eEnt, iRec, ListEXTchain;
  TotalListOrbit:=TotalArray.CellComplex.TotalListOrbit;
  ListGenGRP:=GeneratorsOfGroup(eGRP);
  nbOrbit:=Length(TotalListOrbit[iDim]);
  TotalListCell:=[];
  for iOrbit in [1..nbOrbit]
  do
    ListCell:=[];
    EXTcell:=TotalListOrbit[iDim][iOrbit].EXT;
    FuncInsertCell:=function(eCell)
      local fCell, eInv;
      for fCell in ListCell
      do
        eInv:=eCell.eMat*Inverse(fCell.eMat);
        if First(EXTcell, x->GetPositionAntipodal(EXTcell,x*eInv)=fail)=fail then
          return;
        fi;
      od;
      Add(ListCell, eCell);
    end;
    for eG in TheChain[iOrbit].ListElt
    do
      eCell:=rec(iOrbit:=iOrbit, eMat:=eG, Status:="NO");
      FuncInsertCell(eCell);
    od;
    while(true)
    do
      nbCell:=Length(ListCell);
      IsFinished:=true;
      for iCell in [1..nbCell]
      do
        if ListCell[iCell].Status="NO" then
          ListCell[iCell].Status:="YES";
          IsFinished:=false;
          for eGen in ListGenGRP
          do
            eMat:=ListCell[iCell].eMat*eGen;
            NewCell:=rec(iOrbit:=iOrbit, eMat:=eMat, Status:="NO");
            FuncInsertCell(NewCell);
          od;
        fi;
      od;
      if IsFinished then
        break;
      fi;
    od;
    Append(TotalListCell, ListCell);
  od;
  #
  TotalNbCell:=Length(TotalListCell);
  nbGen:=Length(ListGenGRP);
  ListSign:=List(ListGenGRP, FuncSign);
  #
  ListRec:=[];
  TotalSumVect:=ListWithIdenticalEntries(TotalNbCell, 0);
  FuncInsertChain:=function(TheChain)
    local nbRec, eVect, eRec, iRec;
    nbRec:=Length(ListRec);
    eVect:=SP4Z_GetVectorFromChain(iDim, TotalArray, TotalListCell, TheChain);
    eRec:=rec(eVect:=eVect, TheChain:=TheChain, Status:="NO");
    for iRec in [1..nbRec]
    do
      if ListRec[iRec].eVect=eVect then
        return;
      fi;
    od;
    TotalSumVect:=TotalSumVect + eVect;
    Add(ListRec, eRec);
  end;
  FuncInsertChain(TheChain);
  while(true)
  do
    nbRec:=Length(ListRec);
    IsFinished:=true;
    for iRec in [1..nbRec]
    do
      if ListRec[iRec].Status="NO" then
        ListRec[iRec].Status:="YES";
        IsFinished:=false;
        for iGen in [1..nbGen]
        do
          eGen:=ListGenGRP[iGen];
          eSign:=ListSign[iGen];
          NewChain:=[];
          for eEnt in ListRec[iRec].TheChain
          do
            NewListVal:=eEnt.ListVal*eSign;
            NewListElt:=List(eEnt.ListElt, x->x*eGen);
            fEnt:=rec(ListVal:=NewListVal, ListElt:=NewListElt);
            Add(NewChain, fEnt);
          od;
          FuncInsertChain(NewChain);
        od;
      fi;
    od;
    if IsFinished then
      break;
    fi;
  od;
  #
  TheAverage:=TotalSumVect / Length(ListRec);
  TheChainRet:=GMOD_GetZeroVector(nbOrbit);
  for iCell in [1..TotalNbCell]
  do
    eCell:=TotalListCell[iCell];
    iOrbit:=eCell.iOrbit;
    Add(TheChainRet[iOrbit].ListElt, eCell.eMat);
    Add(TheChainRet[iOrbit].ListVal, TheAverage[iCell]);
  od;
  return ReducedGmoduleVector(TheChainRet);
end;



DoFlowering:=function(ListTopCells, CoveringCells)
  local NewCoveringCells, nbCov, FuncInsertCoveringCell, iCov, eCellCov, eAdjInfo, fMat, EXTcell, NewCell;
#  NewCoveringCells:=List(CoveringCells, x->x);
  NewCoveringCells:=StructuralCopy(CoveringCells);
  nbCov:=Length(CoveringCells);
  Print("nbCov=", nbCov, "\n");
  FuncInsertCoveringCell:=function(eCell)
    local fCell, eVert;
    for fCell in NewCoveringCells
    do
      if TotSet(fCell.EXTcell)=TotSet(eCell.EXTcell) then
        return;
      fi;
    od;
    Add(NewCoveringCells, eCell);
  end;
  for iCov in [1..nbCov]
  do
    eCellCov:=CoveringCells[iCov];
    for eAdjInfo in ListTopCells[eCellCov.iTopCell].ListAdj
    do
      fMat:=eAdjInfo.eEquiv*eCellCov.eMat;
      EXTcell:=ListTopCells[eAdjInfo.iCell].EXT*fMat;
      NewCell:=rec(iTopCell:=eAdjInfo.iCell, eMat:=fMat, EXTcell:=EXTcell);
      FuncInsertCoveringCell(NewCell);
    od;
  od;
  return NewCoveringCells;
end;







#
# Flowering operations
# Take a bunch of cells and extend them to the nearby
#
DoFlowering_attempt:=function(ListTopCells, CoveringCells)
  local NewCoveringCellsCand, NewCoveringCellsTotSet, NewCoveringCellsAtt, nbCov, CoveringCellsTotSet, FuncInsertCoveringCell, iCov, eCellCov, eAdjInfo, fMat, EXTcell, NewCell, TheMax, ListIdx;
  NewCoveringCellsCand:=[];
  NewCoveringCellsTotSet:=[];
  NewCoveringCellsAtt:=[];
  nbCov:=Length(CoveringCells);
  CoveringCellsTotSet:=List(CoveringCells, x->TotSet(x.EXTcell));
  FuncInsertCoveringCell:=function(eCell)
    local eCellTot, pos;
    eCellTot:=TotSet(eCell.EXTcell);
    if Position(CoveringCellsTotSet, eCellTot)<>fail then
      return;
    fi;
    pos:=Position(NewCoveringCellsTotSet, eCellTot);
    if pos<>fail then
      NewCoveringCellsAtt[pos]:=NewCoveringCellsAtt[pos]+1;
      return;
    fi;
    Add(NewCoveringCellsCand, eCell);
    Add(NewCoveringCellsTotSet, eCellTot);
    Add(NewCoveringCellsAtt, 1);
  end;
  for iCov in [1..nbCov]
  do
    eCellCov:=CoveringCells[iCov];
    for eAdjInfo in ListTopCells[eCellCov.iTopCell].ListAdj
    do
      fMat:=eAdjInfo.eEquiv*eCellCov.eMat;
      EXTcell:=ListTopCells[eAdjInfo.iCell].EXT*fMat;
      NewCell:=rec(iTopCell:=eAdjInfo.iCell, eMat:=fMat, EXTcell:=EXTcell);
      FuncInsertCoveringCell(NewCell);
    od;
  od;
  TheMax:=Maximum(NewCoveringCellsAtt);
  ListIdx:=Filtered([1..Length(NewCoveringCellsAtt)], x->NewCoveringCellsAtt[x]=TheMax);
  Print("Collected(NewCoveringCellsAtt) = ", Collected(NewCoveringCellsAtt), "\n");
  return Concatenation(CoveringCells, NewCoveringCellsCand{ListIdx});
end;



#
# Solution of the contracting homotopy.
#
SP4Z_SolutionInComplex:=function(iDim, TotalArray, TheChain, RecOption)
  local nbOrbitM1, nbOrbit, ListVertices, iOrbitM1, eEnt, eG, EXTcell, eVect, CoveringCells, TotalVertexSet, TheSeq, eStartCell, iVert, eVert, eGoodCell, FuncInsertCoveringCell, ListTopCells, LLL_Index, TheDim, AttemptSystemSolution, nbVert, TotalListOrbit, eCell, iCell, pos, uCell, TotalLength, RecSol, ListEqua, IsCorrectFace, ListEXTchain, SolMethods, nbFlowerOper;
  if iDim < 2 then
    Error("iDim is too small");
  fi;
  ListTopCells:=TotalArray.ListTopCells;
  TotalListOrbit:=TotalArray.CellComplex.TotalListOrbit;
  LLL_Index:=TotalArray.CellComplex.LLL_Index;
  TheDim:=Length(TotalListOrbit);
  nbOrbit:=Length(TotalListOrbit[iDim]);
  nbOrbitM1:=Length(TotalListOrbit[iDim-1]);
  if nbOrbitM1 <> Length(TheChain) then
    Error("TheChain is not of the right length");
  fi;
  #
  # Compute initial set of vertices
  #
  TotalLength:=0;
  ListVertices:=[];
  ListEXTchain:=[];
  for iOrbitM1 in [1..nbOrbitM1]
  do
    eEnt:=TheChain[iOrbitM1];
    for eG in eEnt.ListElt
    do
      EXTcell:=TotalListOrbit[iDim-1][iOrbitM1].EXT*eG;
      Add(ListEXTchain, EXTcell);
      TotalLength:=TotalLength+1;
      for eVect in EXTcell
      do
        if GetPositionAntipodal(ListVertices, eVect)=fail then
          Add(ListVertices, eVect);
        fi;
      od;
    od;
  od;
  if RankMat(ListVertices)=4 then
    ListEqua:=[];
  else
    ListEqua:=NullspaceMat(TransposedMat(ListVertices));
  fi;
  IsCorrectFace:=function(EXTcell)
    local eVert;
    if RecOption.SameSingularities=false then
      return true;
    fi;
    if Length(ListEqua)=0 then
      return true;
    fi;
    for eVert in EXTcell
    do
      if First(ListEqua, x->x*eVert<>0)<>fail then
        return false;
      fi;
    od;
    return true;
  end;
  #
  # Compute a first stage covering set
  # We want it as small as possible, but we have
  # no systematic method for building it.
  #
  nbVert:=Length(ListVertices);
  CoveringCells:=[];
  TotalVertexSet:=[];
  FuncInsertCoveringCell:=function(eCell)
    local fCell, eVert;
    for fCell in CoveringCells
    do
      if TotSet(fCell.EXTcell)=TotSet(eCell.EXTcell) then
        return;
      fi;
    od;
    Add(CoveringCells, eCell);
    for eVert in eCell.EXTcell
    do
      if GetPositionAntipodal(TotalVertexSet, eVert)=fail then
        Add(TotalVertexSet, eVert);
      fi;
    od;
  end;
  eStartCell:=rec(iTopCell:=1, eMat:=IdentityMat(4));
  TheSeq:=SP4Z_GetSequenceToRay(ListTopCells, ListVertices[1], eStartCell);
  eGoodCell:=TheSeq[Length(TheSeq)];
  FuncInsertCoveringCell(eGoodCell);
  for iVert in [2..nbVert]
  do
    eVert:=ListVertices[iVert];
    if GetPositionAntipodal(TotalVertexSet, eVert)=fail then
      TheSeq:=SP4Z_GetSequenceToRay(ListTopCells, eVert, eGoodCell);
#      Print("|TheSeq|=", Length(TheSeq), "\n");
      for eCell in TheSeq
      do
        FuncInsertCoveringCell(eCell);
      od;
    fi;
  od;
  #
  # Next stage verifying the inclusions
  # If not then agressively include cells
  #
  for iOrbitM1 in [1..nbOrbitM1]
  do
    eEnt:=TheChain[iOrbitM1];
    for eG in eEnt.ListElt
    do
      EXTcell:=TotalListOrbit[iDim-1][iOrbitM1].EXT*eG;
      pos:=First(CoveringCells, x->IsSubset(TotSet(x.EXTcell), TotSet(EXTcell))=true);
      if pos=fail then
        eGoodCell:=First(CoveringCells, x->GetPositionAntipodal(x.EXTcell, EXTcell[1])<>fail);
        TheSeq:=SP4Z_GetSequenceToCell(ListTopCells, EXTcell, eGoodCell);
        for eCell in TheSeq
        do
          FuncInsertCoveringCell(eCell);
        od;
      fi;
    od;
  od;
  #
  # Procedure for Computing the included cells
  # and solving if that is possible
  #
  AttemptSystemSolution:=function(CoveringCells)
    local LL_Cell, eIter, ListJDim, ListJDimRev, iIter, jDim, ListCell, eGline, FuncInsertCell, eRecCov, jTopCell, fMat, L_Index, eQuad, iOrbitB, eEquiv, uMat, GRA, ListEdges, pos1, pos2, posPt1, posPt2, eEdge, BndImg, nbCell, nbCellM1, ListMatrixDiff, MatrixDiff, eLine, eVectBig, eCell, idx, ePath, ListICell, eRecAsk, eReply, GetMatrixEntry, iDimSrc, ListJDimSrc, TheSol, posNZ, ListPosCell, iLine, ListListBound, ListBound, eFace, ListListBoundTot, posTot, ListTot, ListTotNb, EXTcellTot, ListBoundTot, ListTotRec, TheRecOrig, EXTcont, ListBadCell, lenC, ListLenC, nbCM1, eMat, iEnt, eImg, len, i, eProdMat, eElt, RelListVertices, eChainImg, ListXweight, ListIdx, ListEntries, nbC, DoSave, dimRow, dimCol, FileSave, RecSave, LL_CellKey, ListCellKey, sPerm, TheMethod, PreListCell, PreListCellKey, LIdx, eNormL0;
    LL_Cell:=[];
    LL_CellKey:=[];
    if iDim=2 then
      eIter:=1;
    else
      eIter:=0;
    fi;
    ListJDim:=[];
    ListJDimRev:=ListWithIdenticalEntries(iDim,0);
    idx:=0;
    for iIter in [eIter..2]
    do
      idx:=idx+1;
      jDim:=iIter-2 + iDim;
      Add(ListJDim, jDim);
      ListJDimRev[jDim]:=idx;
      TheMethod:=2;
      ListCell:=[];
      ListCellKey:=[];
      PreListCell:=[];
      PreListCellKey:=[];
      FuncInsertCell:=function(eCell)
        local fCell, eCellTot;
	eCellTot:=TotSet(eCell.EXTcell);
        if Position(ListCellKey, eCellTot)<>fail then
          return;
        fi;
        Add(ListCell, eCell);
        Add(ListCellKey, eCellTot);
      end;
      for eRecCov in CoveringCells
      do
        jTopCell:=eRecCov.iTopCell;
        fMat:=eRecCov.eMat;
        L_Index:=LLL_Index[jDim][jTopCell];
        for eQuad in L_Index
        do
          iOrbitB:=eQuad.eInfo.iOrbit;
          eEquiv:=eQuad.eInfo.eEquiv;
          uMat:=eEquiv*fMat;
          EXTcell:=TotalListOrbit[jDim][iOrbitB].EXT*uMat;
          if IsSubset(TotSet(eRecCov.EXTcell), TotSet(EXTcell))=false then
            Error("Clear error 2");
          fi;
          if IsCorrectFace(EXTcell) then
            uCell:=rec(iOrbit:=iOrbitB, eMat:=uMat, EXTcell:=EXTcell);
	    if TheMethod=1 then
              FuncInsertCell(uCell);
	    fi;
	    if TheMethod=2 then
              Add(PreListCell, uCell);
	      Add(PreListCellKey, TotSet(EXTcell));
	    fi;
	  fi;
        od;
      od;
      if TheMethod=1 then
        sPerm:=SortingPerm(ListCellKey);
        Add(LL_Cell, Permuted(ListCell, sPerm));
        Add(LL_CellKey, Set(ListCellKey));
      fi;
      if TheMethod=2 then
        LIdx:=GetIndexRealizintTheSort(PreListCellKey);
	Add(LL_Cell, PreListCell{LIdx});
	Add(LL_CellKey, Set(PreListCellKey{LIdx})); # The Set is needed to flag the list as a set and get faster algo later
      fi;
      Print("jDim=", jDim, " |ListCell|=", Length(LL_Cell[idx]), "\n");
    od;
    #
    # For dimension 2 this is a shortest path problem.
    # and so we can reduce things and get better solutions.
    #
    if iDim=2 and TotalLength=2 then
      RelListVertices:=List(LL_Cell[1], x->x.EXTcell[1]);
      GRA:=NullGraph(Group(()), Length(LL_Cell[1]));
      ListEdges:=[];
      for eCell in LL_Cell[2]
      do
        pos1:=GetPositionAntipodal(RelListVertices, eCell.EXTcell[1]);
        pos2:=GetPositionAntipodal(RelListVertices, eCell.EXTcell[2]);
        eEdge:=Set([pos1, pos2]);
        Add(ListEdges, eEdge);
        AddEdgeOrbit(GRA, [pos1, pos2]);
        AddEdgeOrbit(GRA, [pos2, pos1]);
      od;
      if IsConnectedGraph(GRA)=false then
        return fail;
      fi;
      posPt1:=GetPositionAntipodal(RelListVertices, ListVertices[1]);
      posPt2:=GetPositionAntipodal(RelListVertices, ListVertices[2]);
      if posPt1=fail or posPt2=fail then
        Error("The point do not belong and that is not allowed");
      fi;
      ePath:=FindShortestPath(GRA, posPt1, posPt2);
      ListICell:=[];
      for iVert in [2..Length(ePath)]
      do
        eEdge:=Set([ePath[iVert-1], ePath[iVert]]);
        iCell:=Position(ListEdges, eEdge);
        Add(ListICell, iCell);
      od;
      LL_Cell[2]:=LL_Cell[2]{ListICell};
      LL_CellKey[2]:=Set(LL_CellKey[2]{ListICell});
    fi;
    nbCellM1:=Length(LL_Cell[ListJDimRev[iDim-1]]);
    nbCell:=Length(LL_Cell[ListJDimRev[iDim]]);
    #
    # Function for finding matrix entry
    #
    GetMatrixEntry:=function(eDim, eRecAsk)
      local EXTcell, iCell, fRec, iOrbitLoc, eQuot, EXT, eList, ePerm, eSignOr, BndImg, xPos;
      EXTcell:=TotalListOrbit[eDim][eRecAsk.iOrbit].EXT*eRecAsk.eMat;
      EXTcellTot:=TotSet(EXTcell);
      iOrbitLoc:=eRecAsk.iOrbit;
      xPos:=ListJDimRev[eDim];
      iCell:=Position(LL_CellKey[xPos], EXTcellTot);
      if iCell=fail then
        Error("No entry found in GetMatrixEntry");
      fi;
      fRec:=LL_Cell[xPos][iCell];
      #
      eQuot:=fRec.eMat*Inverse(eRecAsk.eMat);
      EXT:=TotalListOrbit[eDim][iOrbitLoc].EXT;
      eList:=List(EXT*eQuot, x->GetPositionAntipodal(EXT, x));
      ePerm:=PermList(eList);
      if ePerm=fail then
        Error("Wrong eList");
      fi;
      BndImg:=TotalListOrbit[eDim][iOrbitLoc].BoundaryImage;
      if not(ePerm in BndImg.PermGrp) then
        Error("Belonging error to solve");
      fi;
      if ePerm in BndImg.PermGrpOr then
        eSignOr:=1;
      else
        eSignOr:=-1;
      fi;
      return rec(pos:=iCell, val:=eSignOr*eRecAsk.eSign);
    end;
    #
    # Now building the differential matrix d
    # and the preceding one if that make sense.
    #
    ListJDimSrc:=ListJDim{[2..Length(ListJDim)]};
    ListMatrixDiff:=[];
    for iDimSrc in ListJDimSrc
    do
      nbCM1:=Length(LL_Cell[ListJDimRev[iDimSrc-1]]);
      nbC:=Length(LL_Cell[ListJDimRev[iDimSrc]]);
      ListEntries:=[];
      for eCell in LL_Cell[ListJDimRev[iDimSrc]]
      do
        eLine:=ListWithIdenticalEntries(nbCM1,0);
        BndImg:=TotalListOrbit[iDimSrc][eCell.iOrbit].BoundaryImage;
        for iEnt in [1..Length(BndImg.ListSign)]
        do
          uMat:=BndImg.ListElt[iEnt]*eCell.eMat;
          eRecAsk:=rec(iOrbit:=BndImg.ListIFace[iEnt], eMat:=uMat, eSign:=BndImg.ListSign[iEnt]);
          eReply:=GetMatrixEntry(iDimSrc-1, eRecAsk);
          eLine[eReply.pos]:=eLine[eReply.pos] + eReply.val;
        od;
        ListIdx:=Filtered([1..nbCM1], x->eLine[x]<>0);
        eEnt:=rec(ListCol:=ListIdx, ListVal:=eLine{ListIdx});
        Add(ListEntries, eEnt);
      od;
      MatrixDiff:=rec(nbLine:=nbC, nbCol:=nbCM1, ListEntries:=ListEntries);
      Add(ListMatrixDiff, MatrixDiff);
    od;
    #
    # Build the Vector T_g(dF)
    #
    eVectBig:=ListWithIdenticalEntries(nbCellM1, 0);
    for iOrbitM1 in [1..nbOrbitM1]
    do
      eEnt:=TheChain[iOrbitM1];
      len:=Length(eEnt.ListElt);
      for i in [1..len]
      do
        eRecAsk:=rec(iOrbit:=iOrbitM1, eMat:=eEnt.ListElt[i], eSign:=eEnt.ListVal[i]);
        eReply:=GetMatrixEntry(iDim-1, eRecAsk);
        eVectBig[eReply.pos]:=eVectBig[eReply.pos] + eReply.val;
      od;
    od;
    #
    # Checking that d(T_g (du) ) = 0
    # Also checking that the square of the differential is zero.
    #
    Print("Before formal checks d^2=0 and dx=0\n");
    if iDim>2 then
      eProdMat:=SPARSEMAT_ProductMatrix(ListMatrixDiff[2], ListMatrixDiff[1]);
      if SPARSEMAT_IsZero(eProdMat)=false then
        Error("The matrix product should be zero");
      fi;
      eImg:=SPARSEMAT_ImageVector(ListMatrixDiff[1], eVectBig);
      if First(eImg, x->x<>0)<>fail then
        Error("debug from that point");
        return rec(result:="dx is not zero", eImg:=eImg);
      fi;
    fi;
    Print("After formal checks\n");
    #
    # Now solving the system and storing the image
    #
    if RecOption.opti_L1 then
      ListXweight:=ListWithIdenticalEntries(nbCell,1);
      DoSave:=false;
      if DoSave then
        dimRow:=ListMatrixDiff[2-eIter].nbLine;
        dimCol:=ListMatrixDiff[2-eIter].nbCol;
        FileSave:=Concatenation("CASE_", String(dimRow), "_", String(dimCol), "_MATLAB_spmat");
        SPMAT_PrintMatrixForMatlab(FileSave, ListMatrixDiff[2-eIter]);
        #
        FileSave:=Concatenation("CASE_", String(dimRow), "_", String(dimCol), "_MATLAB_vect");
        SPMAT_PrintVectorForMatlab(FileSave, eVectBig);
        #
        FileSave:=Concatenation("CASE_", String(dimRow), "_", String(dimCol), "_gap");
        RecSave:=rec(ListMatrixDiff:=ListMatrixDiff, eIter:=eIter, ListXweight:=ListXweight, eVectBig:=eVectBig);
        SaveDataToFile(FileSave, RecSave);
      fi;
      TheSol:=GetBestSolution_L1_version2(ListXweight, ListMatrixDiff[2-eIter], eVectBig);
      if DoSave then
        RecSave.TheSol:=TheSol;
        SaveDataToFile(FileSave, RecSave);
      fi;
    elif RecOption.opti_AMP then
      TheSol:=GetAMPSparseSolution(ListMatrixDiff[2-eIter], eVectBig);
    else
      if RecOption.integral then
        TheSol:=SolutionIntMatShort(ListMatrixDiff[2-eIter], eVectBig);
      else
        TheSol:=SolutionIntMatShort(ListMatrixDiff[2-eIter], eVectBig);
        if TheSol=fail then
          TheSol:=SolutionMat(ListMatrixDiff[2-eIter], eVectBig);
        fi;
      fi;
    fi;
    if TheSol=fail then
      return fail;
    fi;
    eNormL0:=Norm_L0(TheSol);
    Print("L0 norm=", eNormL0, "\n");
    eGline:=GMOD_GetZeroVector(nbOrbit);
    for iCell in [1..nbCell]
    do
      if TheSol[iCell]<>0 then
        eCell:=LL_Cell[ListJDimRev[iDim]][iCell];
        iOrbitB:=eCell.iOrbit;
        eElt:=eCell.eMat;
        Add(eGline[iOrbitB].ListVal, TheSol[iCell]);
        Add(eGline[iOrbitB].ListElt, eElt);
      fi;
    od;
    eChainImg:=SP4Z_ComputeImage(iDim, TotalArray, eGline);
    if SP4Z_TestChainEquality(iDim-1, TotalArray, eChainImg, TheChain)=false then
      Error("eGline is actually not a solution");
    fi;
    return rec(result:="success", eGline:=eGline, eNormL0:=eNormL0);
  end;
  nbFlowerOper:=0;
  while(true)
  do
    RecSol:=AttemptSystemSolution(CoveringCells);
    if RecSol<>fail then
      break;
    fi;
    Print("Do Flowering operation nbFlowerOper=", nbFlowerOper, " |CoveringCells|=", Length(CoveringCells), "\n");
    CoveringCells:=DoFlowering(ListTopCells, CoveringCells);
    nbFlowerOper:=nbFlowerOper+1;
    if nbFlowerOper=100 then
      Error("Too many flowering. Debug from here");
    fi;
  od;
  return RecSol;
end;









SP4Z_IsStabilizing:=function(iDim, TotalArray, eGRP, FuncSign, TheChain)
  local TotalListOrbit, PermGrpOr, EXTcell, eGen, eSign, NewChain, eEnt, NewEnt;
  TotalListOrbit:=TotalArray.CellComplex.TotalListOrbit;
  for eGen in GeneratorsOfGroup(eGRP)
  do
    eSign:=FuncSign(eGen);
    NewChain:=[];
    for eEnt in TheChain
    do
      NewEnt:=rec(ListVal:=eEnt.ListVal*eSign,
                  ListElt:=List(eEnt.ListElt, x->x*eGen));
      Add(NewChain, NewEnt);
    od;
    if SP4Z_TestChainEquality(iDim, TotalArray, TheChain, NewChain)=false then
      return false;
    fi;
  od;
  return true;
end;








SP4Z_ComputeHeckeOperators:=function(TotalArray, FuncGroupMembership, TheRatMatrix, eDimMax)
  local EXT, EXTimg, nbVert, eStartCell, TheSeq, eGoodCell, iVert, iDim, eRec, TheGmat, eEquiv, uMat, EXTcell, nbOrbit, fMat, iOrbit, uCell, fRec, ePerm, eQuot, eList, iCell, nbOrbitM1, eMat, len, eVect, i, eOrbit, eVert, eEnt, ListIFace, ListElt, ListSign, iEnt, eSign, iFace, eGmodEnt, eGmodLine, iOrbitM1, lenB, iEntB, eVal, eElt, iOrbitB, ListGRA, GRA, jCell, eInt, eVertImg, nbNonZero, eRecPos, pos, NewTriple, ListVertices, BndImg, eRecCov, ListTopCells, TotalListOrbit, TheDim, GetPositionInOrbit, RecGroup, RecHecke, nbCosMat, LL_GmoduleMatrix, L_GmoduleMatrix, iCosMat, eRecHE, eCosMat, ListRelevantCell, eRecCell, eRelCell, eIter, eProdMat, EXTcellImg, EXTimgCos, eGline, LL_ListBoundaries, L_ListBoundaries, ListBoundaries, TheRecBoundary, ListRecordCoset, FuncInsertRecordCoset, IsFinished, iRecordCoset, nbRecordCoset, eGen, zMat, RecCell, EXTface, lenTot, L_MatrixHistoryOperation, MatrixHistoryOperation, eSet, EXTcellTot, eG, iFaceB, nbOrbitM2, ListPos, EXTcellBig, EXTcellBigTot, iOrbitM2, eG3, nPos, eREC, hMat, eLine, TheChain, fVal, ListRecHE, RecSol, RecOption, TheStab, eGRP, eGRPtr, FuncSign, eChainImg;
  if SP4Z_IsInExtendedGroup(TheRatMatrix)=false then
    Error("The matrix should be in the extended symplectic group");
  fi;
  #
  # Define the necessary variables.
  #
  ListTopCells:=TotalArray.ListTopCells;
  TotalListOrbit:=TotalArray.CellComplex.TotalListOrbit;
  TheDim:=Length(TotalListOrbit);
  #
  # Now computing the action on the polyhedral resolution
  #
  GetPositionInOrbit:=function(iDim, eTriple)
    local nbOrbit, iOrbit, fTriple, test;
    for iOrbit in [1..Length(TotalListOrbit[iDim])]
    do
      for fTriple in TotalListOrbit[iDim][iOrbit].ListTriple
      do
        test:=SP4Z_TestEquivalenceTriple(ListTopCells, fTriple, eTriple);
        if test<>false then
          return rec(iOrbit:=iOrbit, eEquiv:=test);
        fi;
      od;
    od;
    Error("Triple not found, please panic");
  end;
  #
  # Double coset splitting and relevant functionality
  #
  RecGroup:=rec(ListGen:=TotalArray.TotalListGenerators,
                IsInGroup:=FuncGroupMembership);
  RecHecke:=HECKE_DoubleCosetToRightCosets(RecGroup, TheRatMatrix);
  nbCosMat:=Length(RecHecke.ListCoset);
  Print("|ListMat|=", nbCosMat, "\n");
  #
  # The big computation
  #
  LL_GmoduleMatrix:=[];
  L_MatrixHistoryOperation:=[];
  for iDim in [1..eDimMax]
  do
    Print("-------------------------------------\n");
    Print("iDim=", iDim, "\n");
    nbOrbit:=Length(TotalListOrbit[iDim]);
    if iDim > 1 then
      nbOrbitM1:=Length(TotalListOrbit[iDim-1]);
    fi;
    if iDim > 2 then
      nbOrbitM2:=Length(TotalListOrbit[iDim-2]);
    fi;
    L_GmoduleMatrix:=[];
    for iCosMat in [1..nbCosMat]
    do
      TheGmat:=GMOD_GetZeroMatrix(nbOrbit, nbOrbit);
      Add(L_GmoduleMatrix, TheGmat);
    od;
    MatrixHistoryOperation:=[];
    for iOrbit in [1..nbOrbit]
    do
      eLine:=[];
      for iCosMat in [1..nbCosMat]
      do
        Add(eLine, rec(status:="undone"));
      od;
      Add(MatrixHistoryOperation, eLine);
    od;
    for iCosMat in [1..nbCosMat]
    do
      Print("  iCosMat=", iCosMat, " / ", nbCosMat, "\n");
      eCosMat:=RecHecke.ListCoset[iCosMat];
      for iOrbit in [1..nbOrbit]
      do
        Print("    iOrbit=", iOrbit, " / ", nbOrbit, " iCosMat=", iCosMat, "/", nbCosMat, " iDim=", iDim, "\n");
        eOrbit:=TotalListOrbit[iDim][iOrbit];
        EXTimgCos:=List(eOrbit.EXT*eCosMat, RemoveFraction);
        if iDim=1 then
          eVertImg:=EXTimgCos[1];
          eStartCell:=rec(iTopCell:=1, eMat:=IdentityMat(4));
          TheSeq:=SP4Z_GetSequenceToRay(ListTopCells, eVertImg, eStartCell);
          eGoodCell:=TheSeq[Length(TheSeq)];
          EXTcellImg:=ListTopCells[eGoodCell.iTopCell].EXT*eGoodCell.eMat;
          pos:=GetPositionAntipodal(EXTcellImg, eVertImg);
          NewTriple:=rec(iTopCell:=eGoodCell.iTopCell, eMat:=eGoodCell.eMat, eSet:=[pos]);
          eRecPos:=GetPositionInOrbit(iDim, NewTriple);
          eEnt:=rec(ListVal:=[1], ListElt:=[eRecPos.eEquiv]);
          L_GmoduleMatrix[iCosMat].TheMat[iOrbit][eRecPos.iOrbit]:=eEnt;
        elif MatrixHistoryOperation[iOrbit][iCosMat].status="undone" then
          ListIFace:=eOrbit.BoundaryImage.ListIFace;
          ListElt:=eOrbit.BoundaryImage.ListElt;
          ListSign:=eOrbit.BoundaryImage.ListSign;
          len:=Length(ListIFace);
          #
          # Compute the chain
          #
          TheChain:=GMOD_GetZeroVector(nbOrbitM1);
          ListRecHE:=[];
          for iEnt in [1..len]
          do
            iFace:=ListIFace[iEnt];
            eMat:=ListElt[iEnt];
            eSign:=ListSign[iEnt];
            eRecHE:=RecHecke.ProductExpression(eMat*eCosMat);
            Add(ListRecHE, eRecHE);
            eGmodLine:=LL_GmoduleMatrix[iDim-1][eRecHE.iCoset].TheMat[iFace];
            for iOrbitM1 in [1..nbOrbitM1]
            do
              eGmodEnt:=eGmodLine[iOrbitM1];
              lenB:=Length(eGmodEnt.ListVal);
              for iEntB in [1..lenB]
              do
                eVal:=eGmodEnt.ListVal[iEntB];
                uMat:=eGmodEnt.ListElt[iEntB]*eRecHE.gP;
                fVal:=eVal*eSign;
                Add(TheChain[iOrbitM1].ListVal, fVal);
                Add(TheChain[iOrbitM1].ListElt, uMat);
              od;
            od;
          od;
          #
          # Call the solver and do the averaging operation
          #
          TheStab:=TotalListOrbit[iDim][iOrbit].TheStab;
          eGRP:=RecHecke.GetStabilizerOfCoset(TheStab, iCosMat);
          eGRPtr:=Group(List(GeneratorsOfGroup(eGRP), x->Inverse(eCosMat)*x*eCosMat));
          Print("|eGRPtr|=", Order(eGRPtr), "\n");
#          RecOption:=rec(integral:=false, SameSingularities:=true);
#          RecOption:=rec(integral:=false, SameSingularities:=false, DoAverage:=false);
#          RecOption:=rec(integral:=false, SameSingularities:=true, DoAverage:=true, opti_L1:=true, opti_AMP:=false);
          RecOption:=rec(integral:=false, SameSingularities:=true, DoAverage:=true, opti_L1:=false, opti_AMP:=true);
          RecSol:=SP4Z_SolutionInComplex(iDim, TotalArray, TheChain, RecOption);
          if RecSol.result<>"success" then
            Error("The system had no solution");
          fi;
          FuncSign:=function(eSym)
            local EXTcell, eSymB, eList, ePerm, eSignOr;
            EXTcell:=TotalListOrbit[iDim][iOrbit].EXT;
            eSymB:=eCosMat*eSym*Inverse(eCosMat);
            eList:=List(EXTcell, x->GetPositionAntipodal(EXTcell, x*eSymB));
            if Position(eList, fail)<>fail then
              Error("Problem in FuncSign 1");
            fi;
            ePerm:=PermList(eList);
            if not(ePerm in TotalListOrbit[iDim][iOrbit].BoundaryImage.PermGrp) then
              Error("Problem in FuncSign 2");
            fi;
            if ePerm in TotalListOrbit[iDim][iOrbit].BoundaryImage.PermGrpOr then
              eSignOr:=1;
            else
              eSignOr:=-1;
            fi;
            return eSignOr;
          end;
          if SP4Z_IsStabilizing(iDim-1, TotalArray, eGRPtr, FuncSign, TheChain)=false then
            Error("The input chain should be invariant");
          fi;
          if RecOption.DoAverage then
            eGline:=SP4Z_GroupAverage(iDim, TotalArray, eGRPtr, FuncSign, RecSol.eGline);
            eChainImg:=SP4Z_ComputeImage(iDim, TotalArray, eGline);
            if SP4Z_TestChainEquality(iDim-1, TotalArray, eChainImg, TheChain)=false then
              Error("eGline is actually not a solution");
            fi;
            if SP4Z_IsStabilizing(iDim, TotalArray, eGRPtr, FuncSign, eGline)=false then
              Error("The output chain should be invariant");
            fi;
            if First(eGline, x->First(x.ListVal, y->y=0)<>fail)<>fail then
              Error("Let us investigate the zero");
            fi;
          else
            eGline:=RecSol.eGline;
          fi;
          #
          # Now iterating over the stabilizer to build the mappings coherently.
          #
          ListRecordCoset:=[];
          BndImg:=TotalListOrbit[iDim][iOrbit].BoundaryImage;
          FuncInsertRecordCoset:=function(zMat)
            local eList, ePerm, eRecHE, eSignOr, NewLine, NewListVal, NewListElt, NewEnt, NewListRelevantCell, TheInv, ListPair, jOrbit, eG, EXTedge, ListVertices, ListVerticesNb, ePair;
            eList:=List(eOrbit.EXT*zMat, x->GetPositionAntipodal(eOrbit.EXT,x));
            ePerm:=PermList(eList);
            if ePerm=fail then
              Error("Wrong eList");
            fi;
            if not(ePerm in BndImg.PermGrp) then
              Error("Belonging error to solve");
            fi;
            if ePerm in BndImg.PermGrpOr then
              eSignOr:=1;
            else
              eSignOr:=-1;
            fi;
            eRecHE:=RecHecke.ProductExpression(zMat*eCosMat);
            if MatrixHistoryOperation[iOrbit][eRecHE.iCoset].status="done" then
              return;
            fi;
            MatrixHistoryOperation[iOrbit][eRecHE.iCoset]:=rec(status:="done", iCosMat:=iCosMat, zMat:=zMat);
            NewLine:=[];
            TheInv:=Inverse(eRecHE.gP);
            for eEnt in eGline
            do
              NewListVal:=eEnt.ListVal*eSignOr;
              NewListElt:=List(eEnt.ListElt, x->x*TheInv);
              NewEnt:=rec(ListVal:=NewListVal, ListElt:=NewListElt);
              Add(NewLine, NewEnt);
            od;
            L_GmoduleMatrix[eRecHE.iCoset].TheMat[iOrbit]:=NewLine;
            Add(ListRecordCoset, rec(zMat:=zMat, Status:=0));
          end;
          FuncInsertRecordCoset(IdentityMat(4));
          while(true)
          do
            IsFinished:=true;
            nbRecordCoset:=Length(ListRecordCoset);
            for iRecordCoset in [1..nbRecordCoset]
            do
              if ListRecordCoset[iRecordCoset].Status=0 then
                ListRecordCoset[iRecordCoset].Status:=1;
                IsFinished:=false;
                for eGen in GeneratorsOfGroup(TotalListOrbit[iDim][iOrbit].TheStab)
                do
                  zMat:=eGen*ListRecordCoset[iRecordCoset].zMat;
                  FuncInsertRecordCoset(zMat);
                od;
              fi;
            od;
            if IsFinished then
              break;
            fi;
          od;
        fi;
      od;
    od;
    Add(LL_GmoduleMatrix, L_GmoduleMatrix);
    Add(L_MatrixHistoryOperation, MatrixHistoryOperation);
  od;
  return rec(LL_GmoduleMatrix:=LL_GmoduleMatrix, 
             L_MatrixHistoryOperation:=L_MatrixHistoryOperation, 
             TheRatMatrix:=TheRatMatrix, 
             eDimMax:=eDimMax);
end;




SP4Z_GetFuncTestBelong:=function(RecReturn, optGroup)
  local eInvMat, FuncTestBelong1, FuncTestBelong2;
  eInvMat:=RecReturn.eInvMat;
  # Sp4Z
  FuncTestBelong1:=function(eMat)
    if eMat*eInvMat*TransposedMat(eMat)=eInvMat and IsIntegralMat(eMat)=true then
      return true;
    fi;
    return false;
  end;
  # GSp4Z
  FuncTestBelong2:=function(eMat)
    if Position([eInvMat, -eInvMat], eMat*eInvMat*TransposedMat(eMat))<>fail and IsIntegralMat(eMat)=true then
      return true;
    fi;
    return false;
  end;
  if optGroup=1 then
    return FuncTestBelong1;
  else
    return FuncTestBelong2;
  fi;
end;


SP4Z_GetSignature:=function(TotalListOrbit, eDim, iOrbit, eMat)
  local EXT, BndImg, eList, ePerm;
  EXT:=TotalListOrbit[eDim][iOrbit].EXT;
  BndImg:=TotalListOrbit[eDim][iOrbit].BoundaryImage;
  eList:=List(EXT, x->GetPositionAntipodal(EXT, x*eMat));
  ePerm:=PermList(eList);
  if ePerm=fail then
    Error("Wrong eList here");
  fi;
  if not(ePerm in BndImg.PermGrp) then
    Error("Belonging error to solve");
  fi;
  if ePerm in BndImg.PermGrpOr then
    return 1;
  else
    return -1;
  fi;
end;


SP4Z_FindMatchingOrbit:=function(RecHomol, FuncGroupMembershipFI, eDim, iOrbit, eG)
  local EXT, iOrbitFI, eEquiv, eStabMat, zEquiv, eList, ePerm, eSign, BndImg, test, nTriple, eG2, nbOrbitFI, EXTimgCell, eSet, eRecTop, wMat, EXT1, EXT2, EXT3, FindMatchingTopCell, eTriple, fTriple, nbTopCellFI;
  EXT:=RecHomol.TotalArray.CellComplex.TotalListOrbit[eDim][iOrbit].EXT;
  EXT1:=EXT*eG;
  BndImg:=RecHomol.TotalArray.CellComplex.TotalListOrbit[eDim][iOrbit].BoundaryImage;
  eTriple:=RecHomol.TotalArray.CellComplex.TotalListOrbit[eDim][iOrbit].ListTriple[1];
  eG2:=eTriple.eMat*eG;
  nbTopCellFI:=Length(RecHomol.TotalArrayFI.ListTopCells);
  FindMatchingTopCell:=function(iTopCell, eG)
    local iTopCellFI, eTopEquiv, eStabMat, zEquiv, EXT1, EXT2;
    for iTopCellFI in [1..nbTopCellFI]
    do
      eTopEquiv:=RecHomol.L_CorrespTopCell[iTopCellFI];
      if eTopEquiv.iTopCell=iTopCell then
        for eStabMat in RecHomol.TotalArray.ListTopCells[iTopCell].TheStab
        do
          zEquiv:=Inverse(eStabMat*eTopEquiv.eMat)*eG;
          if FuncGroupMembershipFI(zEquiv) then
            EXT1:=RecHomol.TotalArray.ListTopCells[iTopCell].EXT*eG;
            EXT2:=RecHomol.TotalArrayFI.ListTopCells[iTopCellFI].EXT*zEquiv;
            if TotSet(EXT1)<>TotSet(EXT2) then
              Error("Not consistent between EXT1 and EXT2");
            fi;
            return rec(iTopCellFI:=iTopCellFI, eMat:=zEquiv);
          fi;
        od;
      fi;
    od;
    Error("Fail to find corresponding orbit");
  end;
  eRecTop:=FindMatchingTopCell(eTriple.iTopCell, eG2);
  EXTimgCell:=RecHomol.TotalArrayFI.ListTopCells[eRecTop.iTopCellFI].EXT*eRecTop.eMat;
  eSet:=Set(List(EXT1, x->GetPositionAntipodal(EXTimgCell, x)));
  nTriple:=rec(eSet:=eSet, iTopCell:=eRecTop.iTopCellFI, eMat:=eRecTop.eMat);
  nbOrbitFI:=Length(RecHomol.TotalArrayFI.CellComplex.TotalListOrbit[eDim]);
  for iOrbitFI in [1..nbOrbitFI]
  do
    if RecHomol.LL_Correspondence[eDim][iOrbitFI].iOrbit=iOrbit then
      for fTriple in RecHomol.TotalArrayFI.CellComplex.TotalListOrbit[eDim][iOrbitFI].ListTriple
      do
        test:=SP4Z_TestEquivalenceTriple(RecHomol.TotalArrayFI.ListTopCells, fTriple, nTriple);
        if test<>false then
          wMat:=RecHomol.LL_Correspondence[eDim][iOrbitFI].eEquiv*test;
          EXT2:=RecHomol.TotalArray.CellComplex.TotalListOrbit[eDim][iOrbit].EXT*wMat;
          EXT3:=RecHomol.TotalArrayFI.CellComplex.TotalListOrbit[eDim][iOrbitFI].EXT*test;
          if TotSet(EXT2)<>TotSet(EXT3) then
            Error("Non-equality between EXT2 and EXT3");
          fi;
          if TotSet(EXT1)<>TotSet(EXT3) then
            Error("Non-equality between EXT1 and EXT3");
          fi;
          eStabMat:=wMat*Inverse(eG);
          eSign:=SP4Z_GetSignature(RecHomol.TotalArray.CellComplex.TotalListOrbit, eDim, iOrbit, eStabMat);
          return rec(iOrbitFI:=iOrbitFI, eEquiv:=test, eSign:=eSign);
        fi;
      od;
    fi;
  od;
  Error("We did not find the matching orbit");
end;





SP4Z_ComputeHomologyInfo_for_Hecke:=function(TotalArray, FuncGroupMembership, TotalArrayFI, FuncGroupMembershipFI, eDimMax, EliminateInfinity)
  local RecGroup, RecHecke, ListTopCells, TotalListOrbit, TheDim, RecGRoupFI, ListTopCellsFI, nbTopCellFI, ListListFacesCoho, ListStab, TestEquivalenceCells, GetTopCellType, L_Correspondence, LL_Correspondence, FindEquiv, iOrbitFI, RecGroupFI, L_CorrespTopCell, eTriple, uMat, nbOrbitFI, LL_GmoduleMatrix, eProd, len, jOrbit, TotalListOrbitFI, eEquiv, EXTimg, eSet, RecEquiv, iOrbit, nbOrbit, eMat, eRecF, TheGmat, eVal, eBndImg, ListRecOri, BndImg, ListOriRev, iOri, ListOri, EXT, iDim, eCorresp, iTopCell, eRec, i, RecW, eElt, nbOri, eRecOri, LL_BndImg, nbTopCell, FuncTestBelong, fTriple, eSign, ListMat, rnk, NSP, ListSpaces, ListHeckeMatrix, eDim, eSol, DimSpace, optGroup, RecReturn, FindMatchingTopCell, Compute_LL_BndImg, Compute_ListSpaces_PlanA, Compute_LL_GmoduleMatrix, Compute_ListMat_PlanB, Compute_ListMat_PlanA, ThePlan, Compute_ListMat_PlanC, Compute_ListSpaces_PlanC, RecHomol, TheDimFI, Compute_ListSpaces_PlanB;
  RecReturn:=TotalArray.RecReturn;
  optGroup:=TotalArray.optGroup;
  RecGroup:=rec(ListGen:=TotalArray.TotalListGenerators,
                IsInGroup:=FuncGroupMembership);
  ListTopCells:=TotalArray.ListTopCells;
  nbTopCell:=Length(ListTopCells);
  TotalListOrbit:=TotalArray.CellComplex.TotalListOrbit;
  TheDim:=Length(TotalListOrbit);
  #
  RecGroupFI:=rec(ListGen:=TotalArrayFI.TotalListGenerators,
                  IsInGroup:=FuncGroupMembershipFI);
  ListTopCellsFI:=TotalArrayFI.ListTopCells;
  nbTopCellFI:=Length(ListTopCellsFI);
  TotalListOrbitFI:=TotalArrayFI.CellComplex.TotalListOrbit;
  TheDimFI:=Length(TotalListOrbitFI);
  #
  FuncTestBelong:=SP4Z_GetFuncTestBelong(RecReturn, optGroup);
  ListListFacesCoho:=TotalArray.RecReturn.ListListFacesCoho;
  ListStab:=List(ListListFacesCoho[TheDim], x->SymplecticStabilizer(x,FuncTestBelong).MatrGrp);
  TestEquivalenceCells:=function(eCell1, eCell2)
    local eMat, eQuot, EXT1, EXT2;
    if eCell1.iPerf<>eCell2.iPerf then
      return false;
    fi;
    for eMat in ListStab[eCell1.iPerf]
    do
      eQuot:=Inverse(eCell1.g)*eMat*eCell2.g;
      if FuncGroupMembership(eQuot) then
        EXT1:=ListListFacesCoho[TheDim][eCell1.iPerf]*eCell1.g;
        EXT2:=ListListFacesCoho[TheDim][eCell2.iPerf]*eCell2.g;
        if TotSet(EXT1*eQuot)<>TotSet(EXT2) then
          Error("Equivalence error");
        fi;
        return eQuot;
      fi;
    od;
    return false;
  end;
  GetTopCellType:=function(eCellFI)
    local iTopCell, eCell, test;
    for iTopCell in [1..nbTopCell]
    do
      eCell:=ListTopCells[iTopCell];
      test:=TestEquivalenceCells(eCell, eCellFI);
      if test<>false then
        return rec(iTopCell:=iTopCell, eMat:=test);
      fi;
    od;
    Error("We should have found something");
  end;
  #
  L_CorrespTopCell:=List(ListTopCellsFI, GetTopCellType);
  LL_Correspondence:=[];
  for iDim in [1..TheDimFI]
  do
    nbOrbit:=Length(TotalListOrbit[iDim]);
    nbOrbitFI:=Length(TotalListOrbitFI[iDim]);
    FindEquiv:=function(eTriple)
      local iOrbit, fTriple, test;
      for iOrbit in [1..nbOrbit]
      do
        for fTriple in TotalListOrbit[iDim][iOrbit].ListTriple
        do
          test:=SP4Z_TestEquivalenceTriple(ListTopCells, fTriple, eTriple);
          if test<>false then
            return rec(iOrbit:=iOrbit, eEquiv:=test);
          fi;
        od;
      od;
      Error("Triple not found, please panic");
    end;
    L_Correspondence:=[];
    for iOrbitFI in [1..nbOrbitFI]
    do
      eTriple:=TotalListOrbitFI[iDim][iOrbitFI].ListTriple[1];
      EXT:=TotalListOrbitFI[iDim][iOrbitFI].EXT;
      eCorresp:=L_CorrespTopCell[eTriple.iTopCell];
      iTopCell:=eCorresp.iTopCell;
      uMat:=eCorresp.eMat*eTriple.eMat;
      EXTimg:=ListTopCells[iTopCell].EXT*uMat;
      eSet:=Set(List(EXT, x->GetPositionAntipodal(EXTimg, x)));
      fTriple:=rec(eSet:=eSet, eMat:=uMat, iTopCell:=iTopCell);
      RecEquiv:=FindEquiv(fTriple);
      Add(L_Correspondence, RecEquiv);
    od;
    Add(LL_Correspondence, L_Correspondence);
  od;
  Print("LL_Correspondence built\n");
  RecHomol:=rec(TotalArray:=TotalArray,
                TotalArrayFI:=TotalArrayFI, 
                L_CorrespTopCell:=L_CorrespTopCell,
                LL_Correspondence:=LL_Correspondence);
  #
  #
  # Determining orientable orbits
  #
  ListRecOri:=[];
  for iDim in [1..TheDimFI]
  do
    nbOrbitFI:=Length(TotalListOrbitFI[iDim]);
    ListOri:=[];
    for iOrbitFI in [1..nbOrbitFI]
    do
      BndImg:=TotalListOrbitFI[iDim][iOrbitFI].BoundaryImage;
      if Order(BndImg.PermGrp) = Order(BndImg.PermGrpOr) then
        if EliminateInfinity=false then
          Add(ListOri, iOrbitFI);
        else
          if RankMat(TotalListOrbitFI[iDim][iOrbitFI].EXT)=4 then
            Add(ListOri, iOrbitFI);
          fi;
        fi;
      fi;
    od;
    nbOri:=Length(ListOri);
    ListOriRev:=ListWithIdenticalEntries(nbOrbitFI,0);
    for iOri in [1..nbOri]
    do
      ListOriRev[ListOri[iOri]]:=iOri;
    od;
    eRecOri:=rec(nbOri:=nbOri, ListOri:=ListOri, ListOriRev:=ListOriRev, nbOrbit:=nbOrbitFI);
    Add(ListRecOri, eRecOri);
  od;
  Print("ListRecOri built\n");
  #
  # Computing boundaries
  #
  Compute_LL_BndImg:=function()
    local LL_BndImg, iDim, L_BndImg, nbOrbitFI, iOrbitFI, eRecF, BndImg, len, NewListIFace, NewListElt, NewListSign, i, iFace, eElt, RecW, NewSign, NewElt, eBndImg;
    LL_BndImg:=[];
    for iDim in [1..TheDimFI]
    do
      L_BndImg:=[];
      nbOrbitFI:=Length(LL_Correspondence[iDim]);
      for iOrbitFI in [1..nbOrbitFI]
      do
        eRecF:=LL_Correspondence[iDim][iOrbitFI];
        BndImg:=TotalListOrbit[iDim][eRecF.iOrbit].BoundaryImage;
        if iDim>1 then
          len:=Length(BndImg.ListIFace);
          NewListIFace:=[];
          NewListElt:=[];
          NewListSign:=[];
          for i in [1..len]
          do
            iFace:=BndImg.ListIFace[i];
            eElt:=BndImg.ListElt[i]*eRecF.eEquiv;
            RecW:=SP4Z_FindMatchingOrbit(RecHomol, FuncGroupMembershipFI, iDim-1, iFace, eElt);
            NewSign:=BndImg.ListSign[i]*RecW.eSign;
            NewElt:=RecW.eEquiv;
            Add(NewListIFace, RecW.iOrbitFI);
            Add(NewListElt, NewElt);
            Add(NewListSign, NewSign);
          od;
          eBndImg:=rec(ListIFace:=NewListIFace, ListElt:=NewListElt, ListSign:=NewListSign);
        else
          eBndImg:=rec();
        fi;
        Add(L_BndImg, eBndImg);
      od;
      Add(LL_BndImg, L_BndImg);
    od;
    return LL_BndImg;
  end;
  Compute_ListMat_PlanC:=function()
    local ListMatSparse, iDim, eDim1, eDim2, eMat, i2, iOrbit2, eImg, eRecF, BndImg, len, i, iFace, eElt, RecW, NewSign, NewElt, iOrbit1, eEnt, ListIdx, ListEntries;
    ListMatSparse:=[];
    for iDim in [2..TheDimFI]
    do
      eDim1:=ListRecOri[iDim-1].nbOri;
      eDim2:=ListRecOri[iDim].nbOri;
      ListEntries:=[];
      for i2 in [1..eDim2]
      do
        iOrbit2:=ListRecOri[iDim].ListOri[i2];
        eImg:=ListWithIdenticalEntries(eDim1,0);
        eRecF:=LL_Correspondence[iDim][iOrbit2];
        BndImg:=TotalListOrbit[iDim][eRecF.iOrbit].BoundaryImage;
        len:=Length(BndImg.ListIFace);
        for i in [1..len]
        do
          iFace:=BndImg.ListIFace[i];
          eElt:=BndImg.ListElt[i]*eRecF.eEquiv;
          RecW:=SP4Z_FindMatchingOrbit(RecHomol, FuncGroupMembershipFI, iDim-1, iFace, eElt);
          NewSign:=BndImg.ListSign[i]*RecW.eSign;
          NewElt:=RecW.eEquiv;
          iOrbit1:=ListRecOri[iDim-1].ListOriRev[RecW.iOrbitFI];
          if iOrbit1>0 then
            eImg[iOrbit1]:=eImg[iOrbit1] + NewSign;
          fi;
        od;
        ListIdx:=Filtered([1..eDim1], x->eImg[x]<>0);
        eEnt:=rec(ListCol:=ListIdx, ListVal:=eImg{ListIdx});
        Add(ListEntries, eEnt);
      od;
      eMat:=rec(nbLine:=eDim2, nbCol:=eDim1, ListEntries:=ListEntries);
      Add(ListMatSparse, eMat);
    od;
    return ListMatSparse;
  end;
  Compute_ListMat_PlanB:=function()
    local ListMat, iDim, eDim1, eDim2, eMat, i2, iOrbit2, eImg, eRecF, BndImg, len, i, iFace, eElt, RecW, NewSign, NewElt, iOrbit1;
    ListMat:=[];
    for iDim in [2..TheDimFI]
    do
      eDim1:=ListRecOri[iDim-1].nbOri;
      eDim2:=ListRecOri[iDim].nbOri;
      eMat:=[];
      for i2 in [1..eDim2]
      do
        iOrbit2:=ListRecOri[iDim].ListOri[i2];
        eImg:=ListWithIdenticalEntries(eDim1,0);
        eRecF:=LL_Correspondence[iDim][iOrbit2];
        BndImg:=TotalListOrbit[iDim][eRecF.iOrbit].BoundaryImage;
        len:=Length(BndImg.ListIFace);
        for i in [1..len]
        do
          iFace:=BndImg.ListIFace[i];
          eElt:=BndImg.ListElt[i]*eRecF.eEquiv;
          RecW:=SP4Z_FindMatchingOrbit(RecHomol, FuncGroupMembershipFI, iDim-1, iFace, eElt);
          NewSign:=BndImg.ListSign[i]*RecW.eSign;
          NewElt:=RecW.eEquiv;
          iOrbit1:=ListRecOri[iDim-1].ListOriRev[RecW.iOrbitFI];
          if iOrbit1>0 then
            eImg[iOrbit1]:=eImg[iOrbit1] + NewSign;
          fi;
        od;
        Add(eMat, eImg);
      od;
      Add(ListMat, eMat);
    od;
    return ListMat;
  end;
  Compute_ListMat_PlanA:=function(LL_BndImg)
    local ListMat, iDim, eDim1, eDim2, eMat, i2, iOrbit2, BndImg, eImg, len, i, iFace, iOrbit1;
    ListMat:=[];
    for iDim in [2..TheDimFI]
    do
      eDim1:=ListRecOri[iDim-1].nbOri;
      eDim2:=ListRecOri[iDim].nbOri;
      eMat:=[];
      for i2 in [1..eDim2]
      do
        iOrbit2:=ListRecOri[iDim].ListOri[i2];
        eImg:=ListWithIdenticalEntries(eDim1,0);
        BndImg:=LL_BndImg[iDim][iOrbit2];
        len:=Length(BndImg.ListIFace);
        for i in [1..len]
        do
          iFace:=BndImg.ListIFace[i];
          iOrbit1:=ListRecOri[iDim-1].ListOriRev[iFace];
          if iOrbit1>0 then
            eImg[iOrbit1]:=eImg[iOrbit1] + BndImg.ListSign[i];
          fi;
        od;
        Add(eMat, eImg);
      od;
      Add(ListMat, eMat);
    od;
    return ListMat;
  end;
  #
  # Computing Rational Homology groups
  # We directly kill the torsion.
  # maybe later we can take care of it.
  #
  Compute_ListSpaces_PlanC:=function(ListMatSparse)
    local ListSpaces, iDim, eDim, eMat1, eMat2, SparseMatEqua, TheSpace, eRecSpace, ListSparseMat;
    ListSpaces:=[];
    ListSparseMat:=[];
    for iDim in [1..eDimMax]
    do
      eDim:=ListRecOri[iDim].nbOri;
      if iDim>1 then
        eMat1:=ListMatSparse[iDim-1];
      else
        eMat1:=SPARSEMAT_ZeroMatrix(eDim, 0);
      fi;
      if iDim<TheDim then
        eMat2:=SPARSEMAT_Transpose(ListMatSparse[iDim]);
      else
        eMat2:=SPARSEMAT_ZeroMatrix(eDim, 0);
      fi;
      SparseMatEqua:=SPARSEMAT_ColumnConcatenation(eMat1, eMat2);
      Add(ListSparseMat, SparseMatEqua);
#      TheSpace:=LINBOX_Nullspace(SparseMatEqua);
#      eRecSpace:=rec(TheSpace:=TheSpace);
#      Add(ListSpaces, eRecSpace);
    od;
    Print("We have the sparse matrices\n");
    return ListSpaces;
  end;
  Compute_ListSpaces_PlanA:=function()
    local ListSpaces, iDim, eDim, TheKernel, dimKer, TheSpace, TheSpace_res, TheImage_res, TheImageBig, TheImagePre, rnk, NSP, eRecSpace, TheImage;
    ListSpaces:=[];
    for iDim in [1..eDimMax]
    do
      Print("iDim=", iDim, "\n");
      eDim:=ListRecOri[iDim].nbOri;
      if iDim=1 then
        TheKernel:=IdentityMat(eDim);
      else
        if eDim=0 then
          TheKernel:=[];
        else
          if Length(ListMat[iDim-1]) = 0 then
            TheKernel:=IdentityMat(eDim);
          else
            if Length(ListMat[iDim-1][1])=0 then
              TheKernel:=IdentityMat(Length(ListMat[iDim-1]));
            else
              TheKernel:=NullspaceIntMat(ListMat[iDim-1]);
            fi;
          fi;
        fi;
      fi;
      dimKer:=Length(TheKernel);
      if iDim=TheDim then
        if dimKer=0 then
          TheSpace_res:=[];
        else
          TheSpace_res:=IdentityMat(dimKer);
        fi;
        TheImage_res:=[];
      else
        if dimKer > 0 then
          TheImageBig:=ListMat[iDim];
          TheImagePre:=List(TheImageBig, x->SolutionMat(TheKernel, x));
          if Length(TheImagePre)=0 then
            rnk:=0;
          else
            rnk:=RankMat(TheImagePre);
          fi;
          if rnk=dimKer then
            TheImage_res:=IdentityMat(dimKer);
            TheSpace_res:=[];
          else
            if rnk=0 then
              TheImage_res:=[];
              TheSpace_res:=IdentityMat(dimKer);
            else
              NSP:=NullspaceIntMat(TransposedMat(TheImagePre));
              TheImage_res:=NullspaceIntMat(TransposedMat(NSP));
              TheSpace_res:=SubspaceCompletion(TheImage_res, dimKer);
            fi;
          fi;
        else
          TheSpace_res:=[];
          TheImage_res:=[];
        fi;
      fi;
      if Length(TheSpace_res)=0 then
        TheSpace:=[];
      else
        if Length(TheSpace_res[1])<>dimKer then
          Error("Dimension error in the kernel");
        fi;
        TheSpace:=TheSpace_res*TheKernel;
      fi;
      if Length(TheImage_res)=0 then
        TheImage:=[];
      else
        if Length(TheImage_res[1])<>dimKer then
          Error("Dimension error in the image");
        fi;
        TheImage:=TheImage_res*TheKernel;
      fi;
      eRecSpace:=rec(TheKernel:=TheKernel, TheImage_res:=TheImage_res, TheSpace_res:=TheSpace_res, TheSpace:=TheSpace, TheImage:=TheImage);
      Add(ListSpaces, eRecSpace);
    od;
    return ListSpaces;
  end;
  #
  # In this computation, we do not use integer matrices
  # but instead work over the rationals. Should be faster
  # Also, we expressed the cohomology space as the orthogonal
  # of the image in the kernel.
  # question is how to compute those components. We want to avoid
  # the computation of very large SolutionMat calls.
  # So we write Ker = Im + alpha_1 v_1 + ..... + alpha_m v_m
  # 
  # Instead we want to find vectors w_1, ...., w_m such that
  # alpha_i = <v, w_i>
  # The idea is simple. We want the w_i to be zero on H^{orth}, that is
  # on Ker^{orth} + Im.
  # So, the idea is to find the nullspace of a very large matrix that contains
  # both the equations of Kernel and the equations of orthogonality.
  # 
  Compute_ListSpaces_PlanB:=function()
    local ListSpaces, iDim, eDim, TotalListEqua, TheSpace, ProjMat, MatScal, MatInv, eRecSpace;
    ListSpaces:=[];
    for iDim in [1..eDimMax]
    do
      Print("iDim=", iDim, "\n");
      eDim:=ListRecOri[iDim].nbOri;
      TotalListEqua:=[];
      if iDim=1 or eDim=0 then
        # Do not insert anything in the kernel
      else
        if Length(ListMat[iDim-1]) = 0 then
          # Nothing to insert
        else
          if Length(ListMat[iDim-1][1])=0 then
            # No insert done
          else
            Append(TotalListEqua, TransposedMat(ListMat[iDim-1]));
          fi;
        fi;
      fi;
      if iDim=TheDim or eDim=0 then
        # No image computed because no operator or zero dimensional space
      else
        Append(TotalListEqua, ListMat[iDim]);
      fi;
      if eDim=0 then
        TheSpace:=[];
        ProjMat:=[];
      else
        if Length(TotalListEqua)=0 then
          TheSpace:=IdentityMat(eDim);
        else
          TheSpace:=NullspaceMat(TransposedMat(TotalListEqua));
        fi;
        Print("  |TheSpace|=", Length(TheSpace), "\n");
	if Length(TheSpace)=0 then
          ProjMat:=[];
        else
          MatScal:=TheSpace*TransposedMat(TheSpace);
          MatInv:=Inverse(MatScal);
          ProjMat:=TheSpace*MatInv;
        fi;
      fi;
      eRecSpace:=rec(TheSpace:=TheSpace, ProjMat:=ProjMat);
      Add(ListSpaces, eRecSpace);
    od;
    return ListSpaces;
  end;
#  ThePlan:="PlanA";
  ThePlan:="PlanB";
#  ThePlan:="PlanC";
  if ThePlan="PlanA" then
    LL_BndImg:=Compute_LL_BndImg();
    ListMat:=Compute_ListMat_PlanA(LL_BndImg);
    ListSpaces:=Compute_ListSpaces_PlanA();
  elif ThePlan="PlanB" then
    ListMat:=Compute_ListMat_PlanB();
    Print("ListMat computed\n");
#    ListSpaces:=Compute_ListSpaces_PlanA();
    ListSpaces:=Compute_ListSpaces_PlanB();
    Print("ListSpaces computed\n");
  elif ThePlan="PlanC" then
    ListMat:=Compute_ListMat_PlanC();
    Print("ListMat computed\n");
    ListSpaces:=Compute_ListSpaces_PlanC(ListMat);
    Print("ListSpaces computed\n");
  else
    Error("Wrong Plan set");
  fi;
  RecHomol.ListSpaces:=ListSpaces;
  RecHomol.ListMat:=ListMat;
  RecHomol.ListRecOri:=ListRecOri;
  return RecHomol;
end;






SP4Z_GetHeckeHomologyMatrices:=function(RecHomol, FuncGroupMembership, FuncGroupMembershipFI, RecHecke_GmoduleMat)
  local TheRatMatrix, RecGroup, RecHecke, ListTopCells, TotalListOrbit, TheDim, RecGRoupFI, ListTopCellsFI, nbTopCellFI, RecHeckeFI, nbCosMatFI, ListListFacesCoho, ListStab, TestEquivalenceCells, GetTopCellType, L_Correspondence, FindEquiv, iOrbitFI, RecGroupFI, L_CorrespTopCell, eTriple, uMat, nbOrbitFI, LL_GmoduleMatrix, eProd, len, jOrbit, TotalListOrbitFI, eEquiv, EXTimg, eSet, RecEquiv, iOrbit, nbOrbit, eMat, eRecF, TheGmat, eVal, eBndImg, ListRecOri, BndImg, ListOriRev, iOri, ListOri, EXT, iDim, eCorresp, iTopCell, eRec, i, RecW, eElt, nbOri, eRecOri, LL_BndImg, nbTopCell, FuncTestBelong, fTriple, eSign, ListMat, rnk, NSP, ListHeckeMatrix, eDim, eSol, DimSpace, optGroup, RecReturn, eDimMax, Compute_LL_BndImg, Compute_LL_GmoduleMatrix, Compute_ListHeckeMatrix_PlanB, Compute_ListHeckeMatrix_PlanA, ThePlan, Compute_ListHeckeMatrix_PlanC;
  eDimMax:=RecHecke_GmoduleMat.eDimMax;
  TheRatMatrix:=RecHecke_GmoduleMat.TheRatMatrix;
  RecReturn:=RecHomol.TotalArray.RecReturn;
  optGroup:=RecHomol.TotalArray.optGroup;
  RecGroup:=rec(ListGen:=RecHomol.TotalArray.TotalListGenerators,
                IsInGroup:=FuncGroupMembership);
  RecHecke:=HECKE_DoubleCosetToRightCosets(RecGroup, TheRatMatrix);
  ListTopCells:=RecHomol.TotalArray.ListTopCells;
  nbTopCell:=Length(ListTopCells);
  TotalListOrbit:=RecHomol.TotalArray.CellComplex.TotalListOrbit;
  TheDim:=Length(TotalListOrbit);
  #
  RecGroupFI:=rec(ListGen:=RecHomol.TotalArrayFI.TotalListGenerators,
                  IsInGroup:=FuncGroupMembershipFI);
  ListTopCellsFI:=RecHomol.TotalArrayFI.ListTopCells;
  nbTopCellFI:=Length(ListTopCellsFI);
  TotalListOrbitFI:=RecHomol.TotalArrayFI.CellComplex.TotalListOrbit;
  RecHeckeFI:=HECKE_DoubleCosetToRightCosets(RecGroupFI, TheRatMatrix);
  nbCosMatFI:=Length(RecHeckeFI.ListCoset);
  Print("nbCosMatFI=", nbCosMatFI, "\n");
  #
  #
  # Computing differentials with
  # ---Killed G actions
  # ---Killed orientable faces
  #
  Compute_LL_GmoduleMatrix:=function()
    local LL_GmoduleMatrix, iDim, nbOrbitFI, nbOrbit, L_GmoduleMatrix, iCosMatFI, eCosMatFI, iOrbit, eProd, eRecP, RelMatrix, jOrbit, eEnt, i, eMat, eRecF, eVal;
    Print("Computing LL_GmoduleMatrix\n");
    LL_GmoduleMatrix:=[];
    for iDim in [1..eDimMax]
    do
      Print("iDim=", iDim, "\n");
      nbOrbitFI:=Length(TotalListOrbitFI[iDim]);
      nbOrbit:=Length(TotalListOrbit[iDim]);
      L_GmoduleMatrix:=[];
      for iCosMatFI in [1..nbCosMatFI]
      do
        eCosMatFI:=RecHeckeFI.ListCoset[iCosMatFI];
        TheGmat:=GMOD_GetZeroMatrix(nbOrbitFI, nbOrbitFI);
        for iOrbitFI in [1..nbOrbitFI]
        do
          eRec:=RecHomol.LL_Correspondence[iDim][iOrbitFI];
          iOrbit:=eRec.iOrbit;
          eProd:=eRec.eEquiv*eCosMatFI;
          eRecP:=RecHecke.ProductExpression(eProd);
          RelMatrix:=RecHecke_GmoduleMat.LL_GmoduleMatrix[iDim][eRecP.iCoset];
          for jOrbit in [1..nbOrbit]
          do
            eEnt:=RelMatrix.TheMat[eRec.iOrbit][jOrbit];
            for i in [1..Length(eEnt.ListVal)]
            do
              eMat:=eEnt.ListElt[i]*eRecP.gP;
              eRecF:=SP4Z_FindMatchingOrbit(RecHomol, FuncGroupMembershipFI, iDim, jOrbit, eMat);
              eVal:=eEnt.ListVal[i]*eRecF.eSign;
              Add(TheGmat.TheMat[iOrbitFI][eRecF.iOrbitFI].ListElt, eRecF.eEquiv);
              Add(TheGmat.TheMat[iOrbitFI][eRecF.iOrbitFI].ListVal, eVal);
            od;
          od;
        od;
        Add(L_GmoduleMatrix, TheGmat);
      od;
      Add(LL_GmoduleMatrix, L_GmoduleMatrix);
    od;
    return LL_GmoduleMatrix;
  end;
  #
  # Computing differentials with
  # ---Killed G actions
  # ---Killed orientable faces
  #
  Compute_ListHeckeMatrix_PlanA:=function(LL_GmoduleMatrix)
    local ListHeckeMatrix, iDim, nbOri, nbOrbitFI, DimSpace, TheConcat, TheMatHecke, eVect, eVectTot, iOri, eCoeff, iOrbitFI, jOri, jOrbitFI, eSum, iCosMatFI, eSol, eSolRed, eEnt;
    ListHeckeMatrix:=[];
    for iDim in [1..eDimMax]
    do
      nbOri:=RecHomol.ListRecOri[iDim].nbOri;
      nbOrbitFI:=Length(TotalListOrbitFI[iDim]);
      DimSpace:=Length(RecHomol.ListSpaces[iDim].TheSpace);
      TheConcat:=Concatenation(RecHomol.ListSpaces[iDim].TheSpace, RecHomol.ListSpaces[iDim].TheImage);
      TheMatHecke:=[];
      for eVect in RecHomol.ListSpaces[iDim].TheSpace
      do
        eVectTot:=ListWithIdenticalEntries(nbOri,0);
        for iOri in [1..nbOri]
        do
          eCoeff:=eVect[iOri];
          iOrbitFI:=RecHomol.ListRecOri[iDim].ListOri[iOri];
          for jOri in [1..nbOri]
          do
            jOrbitFI:=RecHomol.ListRecOri[iDim].ListOri[jOri];
            eSum:=0;
            for iCosMatFI in [1..nbCosMatFI]
            do
              eEnt:=LL_GmoduleMatrix[iDim][iCosMatFI].TheMat[iOrbitFI][jOrbitFI];
              eSum:=eSum+Sum(eEnt.ListVal);
            od;
            eVectTot[jOri]:=eVectTot[jOri] + eCoeff*eSum;
          od;
        od;
        eSol:=SolutionMat(TheConcat, eVectTot);
        eSolRed:=eSol{[1..DimSpace]};
        Add(TheMatHecke, eSolRed);
      od;
      Add(ListHeckeMatrix, TheMatHecke);
    od;
    return ListHeckeMatrix;
  end;
  Compute_ListHeckeMatrix_PlanB:=function()
    local ListHeckeMatrix, iDim, nbOri, nbOrbit, nbOrbitFI, DimSpace, TheConcat, ListImage, iVect, eVectTot, iOri, iOrbitFI, iCosMatFI, eCosMatFI, eRec, iOrbit, eProd, eRecP, RelMatrix, jOrbit, eEnt, i, eMat, eRecF, jOriFI, eSolRed, eCoeff, TheMatHecke;
    ListHeckeMatrix:=[];
    for iDim in [1..eDimMax]
    do
      Print("iDim=", iDim, "\n");
      nbOri:=RecHomol.ListRecOri[iDim].nbOri;
      nbOrbitFI:=Length(TotalListOrbitFI[iDim]);
      nbOrbit:=Length(TotalListOrbit[iDim]);
      DimSpace:=Length(RecHomol.ListSpaces[iDim].TheSpace);
      TheConcat:=Concatenation(RecHomol.ListSpaces[iDim].TheSpace, RecHomol.ListSpaces[iDim].TheImage);
      ListImage:=[];
      for iVect in [1..DimSpace]
      do
        eVectTot:=ListWithIdenticalEntries(nbOri,0);
        Add(ListImage, eVectTot);
      od;
      for iOri in [1..nbOri]
      do
        iOrbitFI:=RecHomol.ListRecOri[iDim].ListOri[iOri];
        for iCosMatFI in [1..nbCosMatFI]
        do
          eCosMatFI:=RecHeckeFI.ListCoset[iCosMatFI];
          eRec:=RecHomol.LL_Correspondence[iDim][iOrbitFI];
          iOrbit:=eRec.iOrbit;
          eProd:=eRec.eEquiv*eCosMatFI;
          eRecP:=RecHecke.ProductExpression(eProd);
          RelMatrix:=RecHecke_GmoduleMat.LL_GmoduleMatrix[iDim][eRecP.iCoset];
          for jOrbit in [1..nbOrbit]
          do
            eEnt:=RelMatrix.TheMat[eRec.iOrbit][jOrbit];
            for i in [1..Length(eEnt.ListVal)]
            do
              eMat:=eEnt.ListElt[i]*eRecP.gP;
              eRecF:=SP4Z_FindMatchingOrbit(RecHomol, FuncGroupMembershipFI, iDim, jOrbit, eMat);
              eVal:=eEnt.ListVal[i]*eRecF.eSign;
              jOriFI:=RecHomol.ListRecOri[iDim].ListOriRev[eRecF.iOrbitFI];
              if jOriFI>0 then
                for iVect in [1..DimSpace]
                do
                  eCoeff:=RecHomol.ListSpaces[iDim].TheSpace[iVect][iOri];
                  ListImage[iVect][jOriFI]:=ListImage[iVect][jOriFI] + eVal*eCoeff;
                od;
              fi;
            od;
          od;
        od;
      od;
      Print("   ListImage built\n");
      TheMatHecke:=[];
      for eVectTot in ListImage
      do
        eSol:=SolutionMat(TheConcat, eVectTot);
        eSolRed:=eSol{[1..DimSpace]};
        Add(TheMatHecke, eSolRed);
      od;
      Print("   TheMatHecke built\n");
      Add(ListHeckeMatrix, TheMatHecke);
    od;
    return ListHeckeMatrix;
  end;
  Compute_ListHeckeMatrix_PlanC:=function()
    local ListHeckeMatrix, iDim, nbOri, nbOrbit, DimSpace, ListImage, iVect, eVectTot, iOri, iOrbitFI, iCosMatFI, eCosMatFI, eRec, iOrbit, eProd, eRecP, RelMatrix, jOrbit, eEnt, i, eMat, eRecF, jOriFI, eCoeff, TheMatHecke, eLine;
    ListHeckeMatrix:=[];
    for iDim in [1..eDimMax]
    do
      nbOri:=RecHomol.ListRecOri[iDim].nbOri;
      nbOrbit:=Length(TotalListOrbit[iDim]);
      DimSpace:=Length(RecHomol.ListSpaces[iDim].TheSpace);
      Print("iDim=", iDim, " DimSpace=", DimSpace, " nbOri=", nbOri, " nbOrbit=", nbOrbit, "\n");
      ListImage:=[];
      for iVect in [1..DimSpace]
      do
        eVectTot:=ListWithIdenticalEntries(nbOri,0);
        Add(ListImage, eVectTot);
      od;
      for iOri in [1..nbOri]
      do
        iOrbitFI:=RecHomol.ListRecOri[iDim].ListOri[iOri];
        for iCosMatFI in [1..nbCosMatFI]
        do
          eCosMatFI:=RecHeckeFI.ListCoset[iCosMatFI];
          eRec:=RecHomol.LL_Correspondence[iDim][iOrbitFI];
          iOrbit:=eRec.iOrbit;
          eProd:=eRec.eEquiv*eCosMatFI;
          eRecP:=RecHecke.ProductExpression(eProd);
          RelMatrix:=RecHecke_GmoduleMat.LL_GmoduleMatrix[iDim][eRecP.iCoset];
          for jOrbit in [1..nbOrbit]
          do
            eEnt:=RelMatrix.TheMat[eRec.iOrbit][jOrbit];
            for i in [1..Length(eEnt.ListVal)]
            do
              eMat:=eEnt.ListElt[i]*eRecP.gP;
              eRecF:=SP4Z_FindMatchingOrbit(RecHomol, FuncGroupMembershipFI, iDim, jOrbit, eMat);
              eVal:=eEnt.ListVal[i]*eRecF.eSign;
              jOriFI:=RecHomol.ListRecOri[iDim].ListOriRev[eRecF.iOrbitFI];
              if jOriFI>0 then
                for iVect in [1..DimSpace]
                do
                  eCoeff:=RecHomol.ListSpaces[iDim].TheSpace[iVect][iOri];
                  ListImage[iVect][jOriFI]:=ListImage[iVect][jOriFI] + eVal*eCoeff;
                od;
              fi;
            od;
          od;
        od;
      od;
      Print("   ListImage built\n");
      TheMatHecke:=[];
      for iVect in [1..DimSpace]
      do
        eVectTot:=ListImage[iVect];
	eLine:=List(RecHomol.ListSpaces[iDim].ProjMat, x->x*eVectTot);
        Add(TheMatHecke, eLine);
      od;
      Print("   TheMatHecke built\n");
      Add(ListHeckeMatrix, TheMatHecke);
    od;
    return ListHeckeMatrix;
  end;
#  ThePlan:="PlanA";
#  ThePlan:="PlanB";
  ThePlan:="PlanC";
  if ThePlan="PlanA" then
    LL_GmoduleMatrix:=Compute_LL_GmoduleMatrix();
    ListHeckeMatrix:=Compute_ListHeckeMatrix_PlanA(LL_GmoduleMatrix);
  elif ThePlan="PlanB" then
    ListHeckeMatrix:=Compute_ListHeckeMatrix_PlanB();
    Print("ListHeckeMatrix computed\n");
  elif ThePlan="PlanC" then
    ListHeckeMatrix:=Compute_ListHeckeMatrix_PlanC(); # Requires the ProjMat to have been computed
    Print("ListHeckeMatrix computed\n");
  else
    Error("Wrong Plan set");
  fi;
  return rec(ListHeckeMatrix:=ListHeckeMatrix);
end;



SP4Z_GetInfoForSubgroup:=function(FuncGroupMembership, optGroup, LevelSearch)
  local RecReturn, RecBoundary, ListArray, ListTopCells, CellComplex, eRecTop, TotalListGenerators, FuncTestBelong, HomologySpaces;
  RecReturn:=SP4Z_GetList_Faces_Coho();
  FuncTestBelong:=SP4Z_GetFuncTestBelong(RecReturn, optGroup);
  ListArray:=SP4Z_GetFlippingInfo(RecReturn, FuncTestBelong);
  eRecTop:=SP4Z_GetTopCells(RecReturn, FuncTestBelong, ListArray, FuncGroupMembership);
  ListTopCells:=eRecTop.ListTopCells;
  Print("|ListTopCells|=", Length(ListTopCells), "\n");
  TotalListGenerators:=eRecTop.TotalListGenerators;
  Print("|TotalListGenerators|=", Length(TotalListGenerators), "\n");
  CellComplex:=SP4Z_GetCellComplex(RecReturn, FuncTestBelong, ListArray, ListTopCells, LevelSearch);
  return rec(RecReturn:=RecReturn,
             optGroup:=optGroup,
             ListArray:=ListArray,
             ListTopCells:=ListTopCells,
             TotalListGenerators:=TotalListGenerators,
             CellComplex:=CellComplex);
end;


SP4Z_GetInfoForSubgroupFI:=function(TotalArray, FuncGroupMembershipFI, LevelSearch, EliminateInfinity)
  local RecReturn, ListArray, optGroup, FuncTestBelong, eRecTop, ListTopCells, TotalListGenerators, CellComplex, HomologySpaces;
  RecReturn:=TotalArray.RecReturn;
  ListArray:=TotalArray.ListArray;
  optGroup:=TotalArray.optGroup;
  FuncTestBelong:=SP4Z_GetFuncTestBelong(RecReturn, optGroup);
  eRecTop:=SP4Z_GetTopCells(RecReturn, FuncTestBelong, ListArray, FuncGroupMembershipFI);
  ListTopCells:=eRecTop.ListTopCells;
  Print("|ListTopCells|=", Length(ListTopCells), "\n");
  TotalListGenerators:=eRecTop.TotalListGenerators;
  Print("|TotalListGenerators|=", Length(TotalListGenerators), "\n");
  CellComplex:=SP4Z_GetCellComplex(RecReturn, FuncTestBelong, ListArray, ListTopCells, LevelSearch);
  return rec(RecReturn:=RecReturn,
             optGroup:=optGroup,
             ListArray:=ListArray,
             ListTopCells:=ListTopCells,
             TotalListGenerators:=TotalListGenerators,
             CellComplex:=CellComplex);
end;

