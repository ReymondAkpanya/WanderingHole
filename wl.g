LoadPackage("SimplicialSurfaces");

L:=AllTriangularComplexes(IsClosedSurface);
S1:=L[1];
S2:=L[2];
#--------------------------------
#input: an simplicial surface S
#output: a set of all (F,f) whereby F is a Face and f is an edge and 
#WanderingHole can be performed with (F,f)

H:=function(S)
	local K,g,f,M,F,i,j;
	K:=[];
	M:=[];
	for F in Faces(S) do
		for f in Edges(S) do 
			if VerticesOfEdge(S,f)[1] in VerticesOfFace(S,F) and not(VerticesOfEdge(S,f)[2] in VerticesOfFace(S,F)) then 		
				Add(K,[F,f]);
			fi;
			if VerticesOfEdge(S,f)[2] in VerticesOfFace(S,F) and not(VerticesOfEdge(S,f)[1] in VerticesOfFace(S,F)) then
				Add(K,[F,f]);
			fi;
		od;
	od;
	for g in K do
		for i in [1,2,3] do
			for j in [1,2] do
				if FacesOfEdge(S,g[2])[j]  in 
				FacesOfEdge(S,EdgesOfFace(S,g[1])[i]) then
					Add(M,g);
				fi;	
			od;
		od;
	od;
	return M;
end;
#------------------------------------------------------------------
#input: a simplicial surface S,List L where by L[1] is a face and L[2} is 
#an edge
#output : a simplicial surface with an hole where F was placed
 
Hole:=function(S,L)
	S:=CraterCut(S,EdgesOfFace(S,L[1])[1]);
	S:=RipCut(S,EdgesOfFace(S,L[1])[1]);
	S:=SplitCut(S,EdgesOfFace(S,L[1])[1]);
	return S;
end;
#---------------------------------------------------------------------------
#input: a siplicial surface S , List L wherby L[1] is a face and L[2] is 
#an edge
# output : retunrs a simplicial surface after letting the hole wander
WanderingHole:=function(S,L)
	local M,temp, g,h,a,rm;
	#Print("Start");
	if(not(IsClosedSurface(S))) then 
		return "Surface must be closed";
	fi;
	if not(IsTriangularComplex(S)) then
		return "S must be a triangular Complex";	
	fi;
	if Length(Faces(S))<3 then 
		return "S must be a triangular Complex";
	fi;
	if not(Length(L)=2) then 
		return "List L must consist of a Face and an Edge";
	fi;
	if not(L[1] in Faces(S)) then 
		return "L[1] must be a face of S";
	fi;
	if not(L[2] in Edges(S)) then
		return "L[2] must be an edge of S"; 
	fi;
	if not(L in H(S)) then 
		return "[F,f] must be in set H(S)";
	fi;
	#-------------Schritt 1 Loch an der Stelle F
	S:=Hole(S,L);
	
	for g in BoundaryEdges(S) do
		if FacesOfEdge(S,g)[1] in FacesOfEdge(S,L[2]) then
			a:=g;
		fi;
	od;
	S:=RipCut(S,L[2]);
	rm:=[];
	M:=[Edges(S)[Length(Edges(S))],Edges(S)[Length(Edges(S))-1]];
	for g in BoundaryEdges(S) do
		if [a,g] in RipMendableEdgePairs(S) and not( g in M) then
			rm:=[a,g];		fi;
		if [g,a] in RipMendableEdgePairs(S) and not(g in M) then 
			rm:=[g,a];
		fi;
	od;

	S:=RipMend(S,rm);
	
	S:=SplitMend(S,SplitMendableFlagPairs(S)[1]);
	temp:=true;
	for h in RipMendableEdgePairs(S) do
		if h[1] in EdgesOfFace(S,L[1]) and not(h[2] in EdgesOfFace(S,L[1])) and temp=true then
			S:=RipMend(S,h);
			temp:=false;
		fi;
	od;
	S:=CraterMend(S,CraterMendableEdgePairs(S)[2]);
	return S; 
end;

#----------------------------------------------
#function needed for WanderRek, returns a List of all simplicial surface 
#surfaces which can be created by performing a wandering hole
WanderRekHelp:=function(S,K)
	local g,T,a,L;
	for g in H(S) do
		a:=true;
		
T:=PolygonalComplexIsomorphismRepresentatives([WanderingHole(S,g)])[1];		
		if notIso(T,K) then 
			
	Add(K,PolygonalComplexIsomorphismRepresentatives([T])[1]);
			K:=WanderRekHelp(T,K);
		fi;
	od;
	return K;
end;

#--------------------------------------
#returns a list of all surfaces which can be created by performing the 
#wandering hole
WanderRek:=function(S)
	local K;
	K:=PolygonalComplexIsomorphismRepresentatives([S]);
	return WanderRekHelp(S,K);
end;

#---------------------------------------------------------
#input : a simplicial surface S and a list of surfaces L
# returns true if S is not isomorph to any surface in L
#returns false false if there is an isomorph surface in L
notIso:=function(S,L)
	local T,a;
	a:=true;
	for T in L do 
		if IsIsomorphicPolygonalComplex(T,S) then 
			a:=false;
		fi;
	od;
	return a;
end;
