LoadPackage("SimplicialSurfaces");    
Read("wl.g");
       
Wandering:=function(S,Face,Edge)   
	local Neighbour,A,B,EdgeNA,EdgeFA,EdgeNB,EdgeFB,VertN,    
    	VertF,EdgesOfF,VerticesOfE,result,VerticesOfF;
    
        Neighbour:=NeighbourFaceByEdgeNC(S,Face, Edge);  
 	A:=VerticesOfEdgeNC(S,Edge)[1];  
	B:=VerticesOfEdgeNC(S,Edge)[2];  
	EdgeFA:=OtherEdgeOfVertexInFaceNC(S,A,Edge,Face);  
 	EdgeNA:=OtherEdgeOfVertexInFaceNC(S,A,Edge,Neighbour);  
 	EdgeFB:=OtherEdgeOfVertexInFaceNC(S,B,Edge,Face);  	
	EdgeNB:=OtherEdgeOfVertexInFaceNC(S,B,Edge,Neighbour);  
 	VertF:=OtherVertexOfEdgeNC(S,A,EdgeFA);  
 	VertN:=OtherVertexOfEdgeNC(S,A,EdgeNA);  
	if VertF=VertN then
		return fail;
	fi;
   
	VerticesOfE:=ShallowCopy(VerticesOfEdges(S));    
       
 	EdgesOfF:=ShallowCopy(EdgesOfFaces(S));    
 	VerticesOfF:=ShallowCopy(VerticesOfFaces(S));  
       
 	VerticesOfE[Edge]:=Set([VertF,VertN]);    
 	EdgesOfF[Face]:=Set([Edge,EdgeFA,EdgeNA]);    
 	EdgesOfF[Neighbour]:=Set([Edge,EdgeFB,EdgeNB]);    
 	VerticesOfF[Face]:=Set([A,VertF,VertN]);    
 	VerticesOfF[Neighbour]:=Set([B,VertN,VertF]);    
       
 	result:=Objectify(PolygonalComplexType,rec());    
 	SetVerticesOfEdges(result,VerticesOfE);    
 	SetEdgesOfFaces(result,EdgesOfF);    
 	SetVerticesOfFaces(result,VerticesOfF);    
	SetVerticesAttributeOfPolygonalComplex(result,
			VerticesAttributeOfPolygonalComplex(S));    
	SetEdges(result,Edges(S));    
 	SetFaces(result,Faces(S));    
 	SetIsPolygonalSurface(result,true);    
 	SetIsTriangularComplex(result,true);    
    	#return SimplicialSurfaceByDownwardIncidenceNC(VerticesOfE,EdgesOfF);    
 	return result;    
end;    
       
      
WanderingIterativ:=function(S)   
    	local SurfaceStack,edge,surf,FaceR,EdgeR,T;    
 	S:=CanonicalRepresentativeOfPolygonalSurface2(S)[1];  
	SurfaceStack:=[S];    
    	for surf in SurfaceStack do    
#	 	for tupel in Whelp(surf) do 
#		 	T:=Wandering(surf,tupel[1],tupel[2]);  
#			T:=CanonicalRepresentativeOfPolygonalSurface2(T)[1];  
#		 	if not(T in SurfaceStack) then   
#				Add(SurfaceStack,T);    
#			fi;    
#	 	od;
		for edge in Edges(surf) do
			T:=Wandering(surf,FacesOfEdge(surf,edge)[1],edge);
			if T <> fail then
				T:=
				CanonicalRepresentativeOfPolygonalSurface2(T)[1];    
 				if not(T in SurfaceStack) then
					Add(SurfaceStack,T);
				fi;
			fi;
		od;
	od;    
 	return SurfaceStack;    
end;           		
       


WanderingIterativWithoutWaist:=function(S)
     local SurfaceStackW,edgeW,surfW,TW;
        S:=CanonicalRepresentativeOfPolygonalSurface2(S)[1];
        SurfaceStackW:=[S];
        for surfW in SurfaceStackW do
#               for tupel in Whelp(surf) do
#                       T:=Wandering(surf,tupel[1],tupel[2]);
#                       T:=CanonicalRepresentativeOfPolygonalSurface2(T)[1];
#                       if not(T in SurfaceStack) then
#                               Add(SurfaceStack,T);
#                       fi;
#               od;
                for edgeW in Edges(surfW) do
                        TW:=Wandering(surfW,FacesOfEdge(surfW,edgeW)[1],edgeW);
                        if TW <> fail then
				if IsAnomalyFree(TW) and HasNoWaist(TW) then
 	                               	TW:=CanonicalRepresentativeOfPolygonalSurface2(TW)[1];
 					if not(TW in SurfaceStackW) then
                                 	       Add(SurfaceStackW,TW);
                               		 fi;
                      		 fi;
			fi;
                od;
        od;
        return SurfaceStackW;
end;

Found:=function(S,L)
	if S in L then
		return false;
	fi;
	return true;
end;

FoundSurfaces:=function(S)
	local counter, ende,surface,edge,i,T,Foundsurf,Listofsurfaces;
	Listofsurfaces:=AllSimplicialSurfaces(NumberOfFaces(S),
			EulerCharacteristic,2);
	Listofsurfaces:=List(Listofsurfaces,surface->
			CanonicalRepresentativeOfPolygonalSurface2(surface)[1]);
	S:=CanonicalRepresentativeOfPolygonalSurface2(S)[1];
	Foundsurf:=[S];
	i:=0;
	counter:=0;
	ende:=Length(Listofsurfaces);
	if S in Listofsurfaces then
		counter:=1;
	fi;	
	for surface in Foundsurf do
		for edge in Edges(surface) do
			#Print(counter, "=",ende,"\n");
			if counter=ende then 
				return [true, Foundsurf];
			fi;
                        T:=Wandering(surface,FacesOfEdge(surface,edge)[1],edge);
			i:=i+1;
			#Print(T<>fail,i,"\n");
                        if T <> fail then
            			T:=CanonicalRepresentativeOfPolygonalSurface2(T)[1];
                                #Print(Found(T,Listofsurfaces));
				if Found(T,Foundsurf) then
                                       	Add(Foundsurf,T);
					counter:=counter+1;
                                fi;
                        fi;
                od;
        od;
	return [Foundsurf,counter];

end;

FoundSurfacesWithoutWaists:=function(S)
end;
TimingTest:=function()   
   	local S,R;    
 	S:=AllSimplicialSurfaces(10,EulerCharacteristic,2)[1]; 
	R:=Runtime();    
 	WanderingIterativ(S);
 	Print("10: ",Runtime()-R,"\n");    
       
 	S:=AllSimplicialSurfaces(12,EulerCharacteristic, 2)[1];  
   
        R:=Runtime();    
         WanderingIterativ(S);   
         Print("12: ",Runtime()-R,"\n");    
       
end;  
#-------------Liste der Funktionen----------------------

ListOfFunctions:=[Wandering,NeighbourFaceByEdge,VerticesOfEdge,
        OtherEdgeOfVertexInFace,OtherVertexOfEdge,Append,
        SimplicialSurfaceByDownwardIncidence,Filtered,
        EdgesOfFace,VerticesOfEdge,Add,Faces,WanderingIterativ,
        CanonicalRepresentativeOfPolygonalSurface2];


#-----------------------MAYBE-------
#hilf:=function(S,F,E)
#       local L,a,N,g1,g2,g;
#       L:=[];
#        a:=true;
#       N:=NeighbourFaceByEdgeNC(S,F,E);
#       for g1 in Filtered(EdgesOfFaceNC(S,N),g->g<>E) do
#               for g2 in Filtered(EdgesOfFaceNC(S,F),g->g<>E) do
#                       if VerticesOfEdgeNC(S,g1)=VerticesOfEdgeNC(S,g2) 
#then
#                               a:=false;
#                       fi;
#               od;
#       od;
 #      if a then
#               return [F,E];
 #      fi;
 #      return L;
#end;

#Whelp:=function(S)
#       local Wlist,F,g;
#       Wlist:=[];
#       for F in Faces(S) do
#               for g in EdgesOfFaceNC(S,F) do
#                       if hilf(S,F,g)<>[] then
#                               Add(Wlist,hilf(S,F,g));
#                       fi;
#               od;
#       od;
#       return Wlist;
#       #return Filtered(Wlist,g->g<>[]);
#end;
