//////////////////////////////////
// Library for polytopes
//////////////////////////////////

// NPolytope
// INPUT: a polynomial f
// OUTPUT: the Newton polytope of f

NPolytope := function(f)
 return Polytope([Exponents(m) : m in Monomials(f)]);
end function;

// Slices 
// INPUT: a polytope pol, a vector v
// OUTPUT: the slice of pol in the direction of v

Slices := function(pol,v)
 L := Ambient(pol);
 u := Dual(L)!Eltseq(v);
 lis := [u*v : v in Vertices(pol)];
 min := Ceiling(Min(lis));
 max := Floor(Max(lis));
 return [#Points(pol meet HyperplaneToPolyhedron(u,m)) : m in [min..max]];
end function;

// Wdir 
// INPUT: a polytope pol
// OUTPUT: the width directions of pol

Wdir := function(pol)
 m,S := Width(pol);
 dir := [];
 repeat
  v := Random(S);
  Append(~dir,v);
  S := S diff {v,-v};
 until #S eq 0;
 return dir;
end function;


// MovePol
// INPUT: a polytope pol
// OUTPUT: a polytope obtained by translating pol to the first quadrant

MovePol := function(pol);
 L := Ambient(pol);
 ll := Wdir(pol);
 if #ll ge 2 
  then 
   M := Matrix(ll[1..2]);
   if Determinant(M) in {-1,1} 
    then
     pol := pol*Transpose(M);
   end if;
  else
   u := Eltseq(ll[1]);
   B := Matrix(2,1,[u[2],-u[1]]);
   k := Kernel(B).1;
   s := Solution(B,Vector([1]));
   _,i := Min([Width(pol,Dual(L)!Eltseq(s+n*k)) : n in [-100..100]]);
   M := Matrix([u,Eltseq(s+(i-100)*k)]);
   pol := pol*Transpose(M);
  end if;
 ver := Vertices(pol);
 xm := Min([Eltseq(p)[1] : p in ver]);
 ym := Min([Eltseq(p)[2] : p in ver]);
 return pol - L![xm,ym];
end function;


// Hder
// INPUT: a polynomial f, a vector v
// OUTPUT: the derivative of f specified by the vector of exponents v

Hder := function(f,v)
 R := Parent(f);
 Z := ToricLattice(Rank(R));
 cf,mon := CoefficientsAndMonomials(f);
 exp := [Z!Exponents(m) : m in mon];
 g := R!0;
 for i in [1..#exp] do
  e := exp[i]-Z!v;
  if Min(Eltseq(e)) ge 0 
   then 
    m := Monomial(R,Eltseq(e));
    c := &*[Binomial(Eltseq(exp[i])[j],v[j]) : j in [1..#v]]*cf[i];
    g := g + c*m;
  end if;
 end for;
 return g;
end function;


// FindCurves
// INPUT: a polygon pol, a positive integer m, a field Q
// OUTPUT: the linear system of polynomials with coefficients
// in Q, whose monomials have exponents in pol, having multiplicity 
// m at the point 1.

FindCurves := function(pol,m,Q)
 n := Dimension(pol);
 A<[x]> := AffineSpace(Q,n);
 R := CoordinateRing(A);
 S := [Monomial(R,Eltseq(p)) : p in Points(pol)];
 p := [1 : i in [1..n]];
 lis := [];
 for d in [0..m-1] do
  mon := MonomialsOfDegree(R,d);
  Append(~lis,[[Evaluate(Hder(f,Exponents(m)),p) : f in S] : m in mon]);
 end for;
 M := Matrix(&cat lis);
 K := Kernel(Transpose(M));
 d := Dimension(K);
 lis := [];
 if d gt 0 then
  for i in [1..d] do
   c := Eltseq(K.i);
   Append(~lis,&+[c[j]*S[j] : j in [1..#S]]);
  end for;
 end if;
 return lis;
end function;


// FindCurve
// INPUT: a polygon pol, a positive integer m, a field Q
// OUTPUT: the curve corresponding to the first element
// of FindCurves(pol,m,Q)

FindCurve := function(pol,m,Q)
 f := FindCurves(pol,m,Q)[1];
 R := Parent(f);
 A := Spec(R);
 return Curve(A,f);
end function;


// Some functions user to order the
// rays of a two-dimensional fan

Ang := function(a,b)
 a := Eltseq(a);
 b := Eltseq(b);
 na := Sqrt(&+[a[i]^2 : i in [1..#a]]);
 nb := Sqrt(&+[b[i]^2 : i in [1..#b]]);
 return &+[a[i]*b[i] : i in [1..#a]]/(na*nb);
end function;

NextOne := function(a,L)
 m := -1;
 for b in L do
  if Ang(a,b) gt m and Determinant(Matrix([a,b])) gt 0 then
   v := b;
   m := Ang(a,v);
  end if;
 end for;
 return v;
end function;

Reorder := function(L)
 S := [L[1]];
 repeat
  v := NextOne(S[#S],L);
  i := Position(L,v);
  Append(~S,v);
 until #S eq #L;
 return S;
end function;

ToricFromRays := function(ra,Q)
 rr := Reorder(ra);
 F := Fan([Cone(r) : r in [[rr[i],rr[i+1]] : i in [1..#rr-1]] cat [[rr[#rr],rr[1]]]]);
 X<[x]> := ToricVariety(Q,F);
 return X;
end function;


// imat
// INPUT: a toric surface or a sequence of rays
// OUTPUT: the intersection matrix of the toric surface

imat := function(X)
 if Type(X) eq TorVar then
  F := Fan(X);
  ra := Rays(F);
 elif Type(X) eq SeqEnum then
  ra := Reorder(X);
  F := Fan([Cone([ra[i],ra[i+1]]) : i in [1..#ra-1]] cat [Cone([ra[#ra],ra[1]])]);
 end if;
 M := ZeroMatrix(Rationals(),#ra,#ra);
 for i in [1..#ra] do
  ind := [j : j in [1..#ra] | j ne i and Cone([ra[i],ra[j]]) in F];
  v := Eltseq(Kernel(Matrix([ra[i]] cat [ra[j] : j in ind])).1);
  for j in [1..#ra] do
   if j in ind then 
    M[i,j] := 1/Abs(Determinant(Matrix([ra[i],ra[j]])));
   end if;
  end for;
  M[i,i] := v[1]/v[2]*M[i,ind[1]];
 end for;
 return M;
end function;

// qu
// INPUT: a matrix M, a vector a, a vector b
// OUTPUT: the intersection number a.M.Transpose(b)

qu := function(M,a,b)
  K := Parent(M[1,1]);
  r := #Eltseq(a);
  N := Matrix(K,1,r,Eltseq(a))*M*Matrix(K,r,1,Eltseq(b));
  return N[1,1];
end function;


// Cre
// INPUT: a plane curve C
// OUTPUT: the Cremona transform of C 
// based on three singular points together
// with the rational map

Cre := function(C);
 pts := SetToSequence(SingularPoints(C));
 PP<x,y,z> := Ambient(C);
 L := LinearSystem(PP,2);
 if #pts ge 3 then
  mul := [Multiplicity(C,p) : p in SingularPoints(C)];
  pts := [p : p in SingularPoints(C)];
  ParallelSort(~mul,~pts);
  mul := Reverse(mul)[1..3];
  pts := [PP!Eltseq(p) : p in Reverse(pts)[1..3]];
  h := map<PP->PP|Sections(LinearSystem(L,pts))>;  
  C := h(C);
 end if;
 return C,h;
end function;


// EllCur
// INPUT: a polygon pol
// OUTPUT: a minimal model E of the elliptic
// curve C defined by pol together with the
// map C -> E

EllCur := function(pol);
 C := FindCurve(pol,Width(pol),Rationals());
 C1 := ProjectiveClosure(C);
 C := C1;
 steps := [];
 repeat
  C,h := Cre(C);
  Append(~steps,<C,h>);
 until #SingularPoints(C) lt 3;
 pts := Points(C) diff SingularPoints(C);
 equ := DefiningEquations(&*[p[2] : p in steps]);
 d := Gcd(equ);
 h := map<C1->C|[Quotrem(p,d) : p in equ]>;
 if #pts ne 0 then
  p := (Points(C) diff SingularPoints(C))[1];
  E1,g1 := EllipticCurve(C,p);
  E2,g2 := MinimalModel(E1);
  equ := DefiningEquations(h*g1*g2);
  d := Gcd(equ);
  f := map<C1->E2|[Quotrem(p,d) : p in equ]>;
  return E2,f;
 end if;
  E1,g1 := EllipticCurve(C);
  E2,g2 := MinimalModel(E1);
  equ := DefiningEquations(h*g1*g2);
  d := Gcd(equ);
  f := map<C1->E2|[Quotrem(p,d) : p in equ]>;
 return E2,f;
end function;



// OrdFacets
// INPUT: a polygon pol
// OUTPUT: the list of facets of pol 
// ordered according to the increasing 
// slope of the normal direction

OrdFacets := function(pol)
 F := NormalFan(pol);
 ra := Reorder(Rays(F));
 Fa := &cat[[F : F in Facets(pol) | Rays(NormalCone(pol,F))[1] eq p] : p in ra];
 return Fa;
end function;



// PtsCur
// INPUT: the function h: C^2 -> P,
// the equation of C in C^2,
// the map CC -> E, from the closure CC of C to its minimal model E,
// the polygon pol,
// the index i of the point to be calculated
// OUTPUT: the image of the point of V(f) 
// cut out by the i-th facet of the polygon 
// pol via the map h

PtsCur := function(h,f,g,pol,i)
 Fa := OrdFacets(pol);
 R<x,y> := Parent(f);
 A := Spec(R);
 K := FunctionField(A);
 J := DiagonalMatrix([1,-1]);
 F := Fa[i];
 v := Vertices(F);
 w := Eltseq(v[2]-v[1]);
 M := Matrix([w,Eltseq(Solution(Matrix(2,1,[-w[2],w[1]]),Vector([1])))])^(-1);
 if &and[Eltseq(u)[2] le 0 : u in Vertices((pol-v[1])*M)] then
  M := M*J;
 end if;

 mon := [&*[K.i^M[j,i] : i in [1..2]] : j in [1..2]];
 f1 := Numerator(Evaluate(f,mon));
 f1 := Basis(Saturation(Ideal([f1]),x*y))[1];
 C1 := Curve(A,f1);
 p1 := (Points(Scheme(C1,y)) diff {A![0,0]})[1];
 ll := [Evaluate(f,mon) : f in DefiningEquations(h)];
 P := Codomain(h);
 CC := ProjectiveClosure(C1);
 h1 := map<CC->P|ll>;
 q1 := h1(p1);
 q := Eltseq(q1);
 D := Domain(g);
 _,gg := IsWeightedProjectiveSpace(P);
 if gg[#gg] gt 1 then
  if q[2] eq 0 then
   return g(D![0,0,1]);
  else
   return g(D![1,q[3]/q[2]^2,q[4]/q[2]^3]);
  end if;
 else
  return q1;
 end if;
end function;



// PointFace
// INPUT: a polygon pol, a positive integer i
// OUTPUT: the intersection of the affine 
// supporting lines of the two facets adjacent 
// to the i-th facet

PointFace := function(pol,i)
 Fa := OrdFacets(pol);
 ll := [j : j in [1..#Fa] | Dimension(Fa[j] meet Fa[i]) eq 0];
 H := [];
 for j in [1,2] do
  r := Rays(NormalCone(pol,Fa[ll[j]]))[1];
  Append(~H,HyperplaneToPolyhedron(r,Vertices(Fa[ll[j]])[1]*r));
  end for;
 return Points(H[1] meet H[2]);
end function;


// LinRelPols
// INPUT: a sequence of polynomials S
// OUTPUT: the linear relations of 
// the elements of S

LinRelPols := function(S)
  mm := {};
  for p in S do
   mm := mm join Set(Monomials(p));
  end for;
  mm := Sort(Setseq(mm));
  M := Matrix([[MonomialCoefficient(f,m) : m in mm] : f in S]);
  return Basis(Kernel(M));
end function;


// DP1 
// INPUT: a polygon, a positive integer
// OUTPUT: the map h: C^2 -> P(1,1,2,3),
// its image, the minimal model of the 
// elliptic curve defined by pol

DP1 := function(pol,i)
 Q := Rationals();
 q := Eltseq(Setseq(PointFace(pol,i))[1]);
 pol2 := Polytope([Eltseq(p) : p in Vertices(pol)] cat [q]);
 B0 := FindCurves(pol,Width(pol),Q);
 R := Parent(B0[1]);
 B := FindCurves(pol2,Width(pol),Q);
 B := [R!f : f in B];
 if B[1] notin B0 then 
  B := B0 cat [B[1]];
 else
  B := B0 cat [B[2]];
 end if;
 B2 := FindCurves(2*pol2,2*Width(pol),Q);
 B3 := FindCurves(3*pol2,3*Width(pol),Q);
 P<[u]> := WeightedProjectiveSpace(Q,[1,1,2,3]);
 D := Divisor(P,1);
 m2 := RiemannRochBasis(2*D);
 m3 := RiemannRochBasis(3*D);
 mon2 := [Evaluate(f,u[1..2] cat [0,0]) : f in m2 | Evaluate(f,u[1..2] cat [0,0]) ne 0];
 mon3 := [Evaluate(f,u[1..3] cat [0]) : f in m3 | Evaluate(f,u[1..3] cat [0]) ne 0];
 lis2 := [R!Evaluate(f,B cat [0,0]) : f in mon2];
 for f in B2 do
  if #LinRelPols(lis2 cat [R!f]) eq 0 then 
   B := B cat [R!f];
   break;
  end if;
 end for;
 lis3 := [R!Evaluate(f,B cat [0]) : f in mon3];
 for f in B3 do
  if #LinRelPols(lis3 cat [R!f]) eq 0 then 
   B := B cat [R!f];
   break;
  end if;
 end for;
 m6 := RiemannRochBasis(6*D);
 v := Eltseq(LinRelPols([Evaluate(f,B) : f in m6])[1]);
 A := Spec(R);
 h := map<A->P|B>;
 g := &+[v[i]*m6[i] : i in [1..#v]];
 PP<[z]> := ProjectivePlane(Q);
 C := Curve(Scheme(PP,Numerator(Evaluate(g,[0,1,z[2]/z[1],z[3]/z[1]]))));
 E1,f1 := EllipticCurve(C);
 E2,f2 := MinimalModel(E1);
 return h,f1*f2,E2;
end function;



// DP3
// INPUT: a polygon, a vector of three 
// positive integers
// OUTPUT: the map h: C^2 -> P^3,
// its image, the minimal model of the 
// elliptic curve defined by pol

DP3 := function(pol,ind)
 Q := Rationals();
 m := Width(pol);
 ver := [Eltseq(v) : v in Vertices(pol)];
 F := NormalFan(pol);
 ra := Reorder(Rays(F));
 Fa := OrdFacets(pol);
 vv := [i : i in [1..#Fa] | Volume(Fa[i]) eq 1];
 Q := Rationals();
 A<[x]> := AffineSpace(Q,2);
 P<[z]> := ProjectiveSpace(Q,3);
 R := CoordinateRing(A);

 pts := [];
 for i in ind do
  H1 := HyperplaneToPolyhedron(ra[i-1],Vertices(Fa[i-1])[1]*ra[i-1]);
  H2 := HyperplaneToPolyhedron(ra[i+1],Vertices(Fa[i+1])[1]*ra[i+1]);
  Append(~pts,Setseq(Points(H1 meet H2))[1]);
 end for;

 if #pts ge 3 then
  pp := [Polytope(ver cat [Eltseq(p)]) : p in pts[1..3]];
  B := [R!(FindCurves(p,m,Q)[1]) : p in [pol] cat pp];
  ll := [B[i]*B[j]*B[k] : i,j,k in [1..#B] | i le j and j le k];
  mm := {};
  for p in ll do
   mm := mm join Set(Monomials(p));
  end for;
  mm := Sort(Setseq(mm));
  M := Matrix([[MonomialCoefficient(f,m) : m in mm] : f in ll]);
  v := Eltseq(Kernel(M).1);
  mon := [z[i]*z[j]*z[k] : i,j,k in [1..#B] | i le j and j le k];
  f := &+[v[i]*mon[i] : i in [1..#v]];
  Cubic := Scheme(P,f); 
  CubC := Curve(Scheme(Cubic,z[1]));
  h := map<A->P|B>;
  ElC,f := EllipticCurve(CubC, CubC![0,0,0,1]);
  E,g := MinimalModel(ElC);
  punti := [g(f(PtsCur(h,B[1],f,pol,i))) : i in vv];
  return vv,E,punti;
 end if;
end function;




// Der
// INPUT: a polynomial, a vector
// OUTPUT: the derivative of f specified
// by the vector of exponents v

Der := function(f,v)
 R := Parent(f);
 g := f;
 for i in [1..#v] do 
  g := Derivative(g,v[i],i);
 end for;
 return g;
end function;




// imatX
// INPUT: a polygon pol
// OUTPUT: the intersection matrix of X

imatX := function(pol)
 F1 := NormalFan(pol);
 ra1 := Reorder(Rays(F1));
 return DiagonalJoin(imat(ra1),Matrix(Rationals(),[[-1]]));
end function;

// imatS
// INPUT: a polygon pol
// OUTPUT: the intersection matrix of 
// the minimal resolution of X

imatS := function(pol)
 F1 := NormalFan(pol);
 F2 := Resolution(F1);
 ra2 := Reorder(Rays(F2));
 return DiagonalJoin(imat(ra2),Matrix(Rationals(),[[-1]]));
end function;


// qua
// INPUT: a vector A, a vector B, a matrix M, a list of vector lis
// OUTPUT: the intersection product A.M.Transpose(B) modulo 
// the subspace <E : E in lis>

qua := function(A,B,M,lis)
 K := Rationals();
 M := Matrix(K,M);
 n := Nrows(M);
 if #lis eq 0 then
  return (Matrix(K,1,n,Eltseq(A))*M*Matrix(K,n,1,Eltseq(B)))[1,1];
 end if;
 E := ToricLattice(n);
 N := Matrix(K,lis)*M*Transpose(Matrix(K,lis));
 u := Solution(N,Matrix(K,1,n,Eltseq(A))*M*Transpose(Matrix(K,lis)));
 A1 := E!Eltseq(A) - &+[E!lis[i]*Eltseq(u)[i] : i in [1..#lis]];
 u := Solution(N,Matrix(K,1,n,Eltseq(B))*M*Transpose(Matrix(K,lis)));
 B1 := E!Eltseq(B) - &+[E!lis[i]*Eltseq(u)[i] : i in [1..#lis]];
 return (Matrix(K,1,n,Eltseq(A1))*M*Matrix(K,n,1,Eltseq(B1)))[1,1];
end function;


// CinS
// INPUT: a polygon pol
// OUTPUT: a Weil divisor on 
// the minimal resolution of X
// which is linearly equivalent 
// to C

CinS := function(pol)
 K := Rationals();
 F1 := NormalFan(pol);
 F2 := Resolution(F1);
 ra1 := Reorder(Rays(F1));
 ra2 := Reorder(Rays(F2));
 ll := &cat[[Volume(F) : F in Facets(pol) | Rays(NormalCone(pol,F))[1] eq p] : p in ra1];
 M := imatS(pol);
 n := Nrows(M);
 E := ToricLattice(n);
 m := Width(pol);
 ind := [i : i in [1..#ra2] | ra2[i] in ra1];
 v := &+[ll[i]*E.ind[i] : i in [1..#ind]] + m*E.n;
 return Solution(M,Matrix(K,1,n,Eltseq(v)));
end function;


// AdjSys
// INPUT: a polygon pol
// OUTPUT: a Weil divisor C on 
// the minimal resolution of X 
// together with the prime components 
// of K + C 

AdjSys := function(pol)
 m := Width(pol);
 K := Rationals();
 F1 := NormalFan(pol);
 F2 := Resolution(F1);
 ra1 := Reorder(Rays(F1));
 ra2 := Reorder(Rays(F2));
 L1 := ToricLattice(#ra1);
 L2 := ToricLattice(#ra2);
 P1 := Transpose(Matrix(ra1));
 P2 := Transpose(Matrix(ra2));
 cla := [];
 R := FindCurve(pol,m,K);
 f := Equation(R);
 vv := [Eltseq(Matrix(1,2,Exponents(m))*P2) : m in Monomials(f)];
 den := [Min([v[i] : v in vv]) : i in [1..#ra2]];
 v := Eltseq(L2!vv[1]-L2!den) cat [-m];
 Append(~cla,v);
 D := [-Min([v*u : u in Vertices(pol)]) : v in ra1];
 Kpol := Polytope(InteriorPoints(pol));
 R := FindCurve(Kpol,m-1,K);
 A := Ambient(R);
 lis := [C : C in PrimeComponents(R) | #Monomials(Equation(C)) gt 1];
 mul := [Multiplicity(C,A![1,1]) : C in lis];
 ll := [Equation(C) : C in lis];
 for i in [1..#ll] do
  vv := [Eltseq(Matrix(1,2,Exponents(m))*P2) : m in Monomials(ll[i])];
  den := [Min([v[i] : v in vv]) : i in [1..#ra2]];
  v := Eltseq(L2!vv[1]-L2!den) cat [-mul[i]];
  Append(~cla,v);
 end for;
 return cla;
end function;


// MultAdjSys
// INPUT: a polygon pol
// OUTPUT: the multiplicities of the curves 
// in K_S + C

MultAdjSys := function(pol)
 m := Width(pol);
 Kpol := Polytope(InteriorPoints(pol));
 f := Equation(FindCurve(Kpol,m-1,Rationals()));
 return [g[2] : g in Factorization(f) | #Monomials(g[1]) gt 1];
end function;


// NpolsAdjSys
// INPUT: a polygon pol
// OUTPUT: the Newton polygons of the curves 
// in K_S + C

NpolsAdjSys := function(pol)
 m := Width(pol);
 Kpol := Polytope(InteriorPoints(pol));
 f := Equation(FindCurve(Kpol,m-1,Rationals()));
 return [NPolytope(g[1]) : g in Factorization(f) | #Monomials(g[1]) gt 1];
end function;


// PolsAdjSys:
// INPUT: a polygon
// OUTPUT: equations of the curves 
// in K_S + C

PolsAdjSys := function(pol)
 m := Width(pol);
 Kpol := Polytope(InteriorPoints(pol));
 f := Equation(FindCurve(Kpol,m-1,Rationals()));
 return [g[1] : g in Factorization(f) | #Monomials(g[1]) gt 1];
end function;


// imatZ
// INPUT: a polygon pol
// OUTPUT: the intersection matrix of 
// the minimal resolution Z of Y

imatZ := function(pol)
 cur := AdjSys(pol);
 M := imatS(pol);
 C := cur[1];
 cur := cur[2..#cur];
 E := ToricLattice(#C);
 n := Dimension(E);
 repeat
  ll := [i : i in [1..n] | qua(E.i,C,M,[]) eq 0 and qua(E.i,E.i,M,cur) eq -1];
  if #ll ne 0 then
   cur := cur cat [Eltseq(E.i) : i in ll];
  end if;
 until #ll eq 0;
 return Matrix(n,n,[qua(A,B,M,cur) : A,B in Basis(E)]);
end function;


// RootLat
// INPUT: a polygon pol
// OUTPUT: root lattice of 
// (-2)-curves on the surface Z

RootLat := function(pol)
 cur := AdjSys(pol);
 M := imatS(pol);
 C := cur[1];
 cur := cur[2..#cur];
 E := ToricLattice(#C);
 n := Dimension(E);
 repeat
  ll := [i : i in [1..n] | qua(E.i,C,M,[]) eq 0 and qua(E.i,E.i,M,cur) eq -1];
  if #ll ne 0 then
   cur := cur cat [Eltseq(E.i) : i in ll];
  end if;
 until #ll eq 0;
 lis := [qua(A,B,M,cur) : A,B in Basis(E) | qua(A,A,M,cur) eq -2 and qua(B,B,M,cur) eq -2];
 r := Floor(Sqrt(#lis));
 N := -Matrix(r,r,lis);
 return CartanName(N);
end function;


// RootR
// INPUT: a polygon pol
// OUTPUT: root rank of 
// (-2)-curves on the surface Z

RootR := function(pol)
 cur := AdjSys(pol);
 M := imatS(pol);
 C := cur[1];
 cur := cur[2..#cur];
 E := ToricLattice(#C);
 n := Dimension(E);
 repeat
  ll := [i : i in [1..n] | qua(E.i,C,M,[]) eq 0 and qua(E.i,E.i,M,cur) eq -1];
  if #ll ne 0 then
   cur := cur cat [Eltseq(E.i) : i in ll];
  end if;
 until #ll eq 0;
 lis := [qua(A,B,M,cur) : A,B in Basis(E) | qua(A,A,M,cur) eq -2 and qua(B,B,M,cur) eq -2];
 r := Floor(Sqrt(#lis));
 return r;
end function;


// imatContr
// INPUT: a polygon pol
// OUTPUT: intersection matrix
// of curves in K + C

imatContr := function(pol)
 cur := AdjSys(pol);
 M := imatS(pol);
 M1 := Matrix(#cur,#cur,[qua(A,B,M,[]) : A,B in cur]);
 C := cur[1];
 cur := cur[2..#cur];
 E := ToricLattice(#C);
 n := Dimension(E);
 repeat
  ll := [i : i in [1..n] | qua(E.i,C,M,[]) eq 0 and qua(E.i,E.i,M,cur) eq -1];
  if #ll ne 0 then
   cur := cur cat [Eltseq(E.i) : i in ll];
  end if;
 until #ll eq 0;
 return M1,Matrix(#cur,#cur,[qua(A,B,M,[]) : A,B in cur]);
end function;


// imatY
// INPUT: a polygon pol
// OUTPUT: the intersection matrix of Y

imatY := function(pol)
 cur := AdjSys(pol);
 M := imatS(pol);
 C := cur[1];
 cur := cur[2..#cur];
 E := ToricLattice(#C);
 n := Dimension(E);
 ll := [Eltseq(E.i) : i in [1..n] | qua(E.i,C,M,[]) eq 0];
 cur := cur cat ll;
 r := n-#ll;
 return Matrix(r,r,[qua(A,B,M,cur) : A,B in Basis(E) | qua(A,C,M,[]) ne 0 and qua(B,C,M,[]) ne 0]);
end function;


// MapToY
// INPUT: a polygon pol
// OUTPUT: the map Cl(S) -> Cl(Y),
// where S is the minimal resolution of X

MapToY := function(pol)
 cur := AdjSys(pol);
 M := imatS(pol);
 C := cur[1];
 cur := cur[2..#cur];
 E := RSpace(Integers(),#C);
 n := Dimension(E);
 ll := [Eltseq(E.i) : i in [1..n] | qua(E.i,C,M,[]) eq 0];
 cur := cur cat ll cat [Eltseq(v) : v in Basis(Kernel(M))];
 Cl,f := quo<E|[E!v : v in cur]>;
 Mf := Matrix([Eltseq(f(v)) : v in Basis(E)]);
 bas := [Solution(Mf,Vector(Eltseq(b))) : b in Basis(Cl)];
 MY := Matrix(#bas,#bas,[qua(a,b,M,cur) : a,b in bas]);
 return Cl,f,MY;
end function;


// ImgDiv
// INPUT: a polygon pol
// OUTPUT: the images in Y
// of the prime invariant divisors 
// of X and of the exceptional divisor

ImgDiv := function(pol)
 F1 := NormalFan(pol);
 F2 := Resolution(F1);
 ra1 := Reorder(Rays(F1));
 ra2 := Reorder(Rays(F2));
 n := #ra2+1;
 E := RSpace(Integers(),n);
 ind := [i : i in [1..#ra2] | ra2[i] in ra1] cat [n];
 Cl,f := MapToY(pol);
 return [f(E.i) : i in ind];
end function;


// resC
// INPUT: a polygon pol, 
// the corresponding elliptic curve E,
// the points cut out on E by the facets of pol of length 1
// OUTPUT: the image of a basis of Cl(Y)

resC := function(pol,E,ff,pts)
 D := ImgDiv(pol);
 M := Matrix([D[i] : i in ff]);
 n := Ncols(M);
 N := Solution(M,IdentityMatrix(Integers(),n));
 return [&+[pts[i]*Eltseq(r)[i] : i in [1..#pts]] : r in Rows(N)];
end function;



// SearchPoints
// INPUT: a polygon pol
// OUTPUT: a side of pol which corresponds
// to a (-1)-curve on X and on Y

SearchPoints := function(pol)
 m := Width(pol);
 MX := imatX(pol);
 MY := imatY(pol);
 F := NormalFan(pol);
 ra := Reorder(Rays(F));
 Fa := &cat[[F : F in Facets(pol) | Rays(NormalCone(pol,F))[1] eq p] : p in ra];
 vv := [i : i in [1..#Fa] | Volume(Fa[i]) eq 1];
 ind := [i : i in [1..Nrows(MX)] | MX[i,i] eq MY[i,i] and MY[i,i] eq -1];
 if #ind gt 0 then
  return ind[1];
  else return 0;
 end if;
end function;


// Findroots
// INPUT: a polygon pol
// OUTPUT: the virtual
// (-2)-classes of Z which intersect 
// non-negatively all the (-2)-curves

FindRoots := function(pol)
 cur := AdjSys(pol);
 C := cur[1];
 M := imatS(pol);
 E := RSpace(Integers(),#C);
 n := Dimension(E);
 repeat
  ll := [i : i in [1..n] | qua(E.i,C,M,[]) eq 0 and qua(E.i,E.i,M,cur) eq -1];
  if #ll ne 0 then
   cur := cur cat [Eltseq(E.i) : i in ll];
  end if;
 until #ll eq 0;
 rootZ := [Eltseq(E.i) : i in [1..n] | qua(E.i,C,M,[]) eq 0 and qua(E.i,E.i,M,cur) eq -2];
 ker := Kernel(Matrix(Integers(),M*Transpose(Matrix([C]))));
 rel := cur cat [Eltseq(v) : v in Basis(Kernel(M))];
 Q,f := quo<ker|[ker!v : v in rel]>;
 nrootZ := [f(v) : v in rootZ];
 U := Matrix(Basis(ker));
 N := Matrix([f(v) : v in Basis(ker)]);
 bas := [Solution(N,Q.i)*U : i in [1..Ncols(N)]];
 mm := Matrix(8,8,[qua(a,b,M,rel) : a,b in bas]); 
 E8 := Lattice(IdentityMatrix(Rationals(),8),-mm);
 EE := RSpace(E8);
 Q2,g := quo<EE|nrootZ>;
 N2 := Matrix([g(v) : v in Basis(EE)]);
 rr := ShortestVectors(E8) cat [-v : v in ShortestVectors(E8)];
 beta := Setseq({g(r) : r in rr | g(r) ne Zero(Q2)});
 sol := [Inverse(g)(b) : b in beta];
 ro := [Eltseq(Solution(N,Vector(b))*U) : b in sol];
 Cl,h := MapToY(pol);
 return [h(r) : r in ro],beta;
end function;



// IsPolyhedralPrime
// INPUT: a sequence of roots, their restrictions to C, 
// the curve C, res(C), a prime p
// OUTPUT: true if p is polyhedral, false otherwise


IsPolyhedralPrime := function(roots,ImgRoots,C,ImgC,p)
 E := ChangeRing(Curve(ImgC),GF(p));
 q := E!ImgC;
 subC := {q};
 repeat
  n := #subC;
  Include(~subC,(n+1)*q);
 until #subC eq n;
 Cl := Parent(roots[1]);
 NewCur := [C] cat [roots[i] : i in [1..#roots] | E!ImgRoots[i] in subC];
 Cl := AbelianGroup(Moduli(Cl));
 NewCur := sub<Cl|[Cl!Eltseq(p) : p in NewCur]>;
 if TorsionFreeRank(sub<Cl|NewCur>) + 1 eq TorsionFreeRank(Cl) then
  return true;
 else
  return false;
 end if;
end function;


// NonPolyhedralPrimes
// INPUT: a polygon pol, a positive integer n
// OUTPUT: the non-polyhedral primes
// associated to pol in the interval [2,n]

NonPolyhedralPrimes := function(pol,n)
 Cl,g := MapToY(pol);
 C := FindCurve(pol,Width(pol),Rationals());
 A := Ambient(C);
 f := Equation(C);
 E,u := EllCur(pol);
 h := map<A->Ambient(E) | [Evaluate(p,[A.1,A.2,1]) : p in DefiningEquations(u)]>;
 ff := [i : i in [1..#Vertices(pol)] | Volume(OrdFacets(pol)[i]) eq 1];
 pts := [E!PtsCur(h,f,u,pol,i) : i in ff];
 B := resC(pol,E,ff,pts);
 roots := FindRoots(pol);
 ImgRoots := [&+[Eltseq(v)[i]*B[i] : i in [1..#B]] : v in roots];
 C := g(CinS(pol));
 ImgC := &+[Eltseq(C)[i]*B[i] : i in [1..#B]];
 goodp := {};
 for p in PrimesInInterval(2,n) do
  if p notin BadPrimes(E) then
  ls := FindCurves(pol,Width(pol),GF(p));
   if #ls eq 1 then f := ls[1]; 
    if NPolytope(f) eq pol and not IsPolyhedralPrime(roots,ImgRoots,C,ImgC,p)
     then Include(~goodp,p);
    end if; 
   end if;
  end if;
 end for;
 return goodp;
end function;


// PrimRep
// INPUT: a a polygon pol
// OUTPUT: a primitive vector which represents p

PrimRep := function(p)
 q := Eltseq(p);
 d := Lcm([Denominator(c) : c in q]);
 return [d*a : a in q];
end function;


// Bprimes
// INPUT: a polygon pol
// OUTPUT: if res(C) has finite order it returns
// the union of the following subsets of primes:
// - bad primes for the Newton polygon of C
// - bad primes for a Weierstrass model E of C
// - bad primes for the map C -> E
// - primes for which there are more effective
// roots than in characteristic 0.

Bprimes := function(pol)
 E,u := EllCur(pol);
 Cl,g := MapToY(pol);
 C := FindCurve(pol,Width(pol),Rationals());
 A := Ambient(C);
 f := Equation(C);
 f := Lcm([Denominator(c) : c in Coefficients(f)])*f;
 h := map<A->Ambient(E) | [Evaluate(p,[A.1,A.2,1]) : p in DefiningEquations(u)]>;
 ff := [i : i in [1..#Vertices(pol)] | Volume(OrdFacets(pol)[i]) eq 1];
 pts := [E!PtsCur(h,f,u,pol,i) : i in ff];
 B := resC(pol,E,ff,pts);
 roots := FindRoots(pol);
 ImgRoots := [&+[Eltseq(v)[i]*B[i] : i in [1..#B]] : v in roots];
 C := g(CinS(pol));
 ImgC := &+[Eltseq(C)[i]*B[i] : i in [1..#B]];
 n := Order(ImgC);
 if n eq 0 then return false; end if;
 R := Parent(f);
 num1 := [Numerator(MonomialCoefficient(f,Monomial(R,Eltseq(m)))) : m in Vertices(NPolytope(f))];
 bad1 := Set(PrimeDivisors(Lcm(num1)));
 bad2 := Set(BadPrimes(E));
 bad3 := Set(&cat[PrimeFactors(Lcm([Denominator(c) : c in Coefficients(g)])) : g in DefiningEquations(u)]);
 pp1 := [PrimRep(p) : p in ImgRoots];
 pp2 := [PrimRep(p) : p in [i*ImgC : i in [0..n-1]]];
 S := {Minors(Matrix([a,b]),2) : a in pp1, b in pp2};
 num2 := {Gcd([Numerator(u) : u in Eltseq(p)]) : p in S};
 bad4 := &join{Set(PrimeDivisors(n)) : n in num2 | n ne 0};
 return bad1 join bad2 join bad3 join bad4;
end function;


