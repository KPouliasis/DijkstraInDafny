class Pair <U,V>{
  var fst:U;
  var snd:V;
  // ghost var Repr: set<object>;
  constructor Init(x:U,y:V) 
  modifies this;
  ensures fst==x;
  ensures snd==y;
  {
    fst:=x;
    snd:=y;
   }
  function method getfst():U
  reads this;
  {
     fst
     
   }
  function method getsnd():V
  reads this;
  {
    
    snd
  }
  
}
class PriorityQueue <T(==)> {
 var N: int;  // capacity
 var n: int;  // current size
 ghost var Repr: set<object>;  // set of objects that make up the representation of a PriorityQueue
 ghost var keys:map <T,int>;
 ghost var values:set <T>;
 ghost var latest:Pair<int,T>;
 var a: array <Pair<int,T>>;  // private implementation of PriorityQueue




 predicate Valid
   reads this, Repr,a;
 {
   MostlyValid 
  && (forall j :: 2 <= j && j <= n ==> a[j/2].getfst() <= a[j].getfst())
 }

 predicate MostlyValid
   reads this, Repr,a;
 {
   this in Repr && a in Repr && a != null&& n <= N && 0 <= n &&a.Length == N+1&& (forall i::1<=i<=n ==>(a[i] in Repr) && 
     (a[i] !=null)) &&(forall t::t in keys <==> t in values) 
     //&& (forall x:: (x in values <==>(exists i::(1<=i<=n && x==a[i].snd))))
     && (forall i,j::1<=i<j<=n ==> a[i].snd!=a[j].snd) &&
     (forall i::1<=i<=n ==> (a[i].snd in keys && keys[a[i].snd]==a[i].fst))
  
    //&& (forall x:: (x in Repr ==> x !in values)) && (forall x:: (x in values ==> x !in Repr))
    //a.Length == N+1 &
  // 0 <= n && n <= N
 }
//method  mapfromelems() returns (arraymap: map <T,int>)
// requires Valid;
 //reads this,a;




 method Init(capacity: int)
   requires 0 <= capacity;
   modifies this;
   ensures  fresh(Repr - {this});
   ensures values=={};
   ensures keys ==map[];
    ensures values =={} && keys==map[] && (forall x:: x in values <==> x in keys);
   ensures n==0;
   ensures N == capacity;
   ensures Valid;
  // ensures forall x:: x in values <==> x in keys;
  // ensures n==0;
 {
   N := capacity;
   a := new Pair<int,T>[N+1];
   n := 0;
   values:={};
   keys:=map[];
   Repr := {this};
   Repr := Repr + {a};
   assert values =={};
   assert keys==map[];
   assert forall x:: x in values <==> x in keys;
   
 }
 method Insert(x: int,t:T)
   requires Valid && n < N;
  
   requires t !in values;
   requires t !in keys;
   requires (forall x:: x in values <==> x in keys);
  
  // requires t !in Repr;
   modifies this, a;
   ensures fresh(Repr - old(Repr));
   ensures values== old(values) +{t};
  
   ensures Repr-old(Repr)=={latest};
  
   
   ensures n == old(n) + 1 && N == old(N);
   ensures x==old(x);
   ensures Valid;
  // ensures (forall x:: x in values <==> x in keys);
  // ensures Valid ;
  //ensures 
  
   //ensures 
  
 
 { 
  // assert forall i::1<=i<=n==> a[i].snd!=t;
   assert  MostlyValid ==> (forall i::1<=i<=n ==> a[i].snd in keys && keys[a[i].snd]==a[i].fst) ;
   n := n + 1;
   a[n] := new Pair.Init(x,t);
   values:=values+{t};
   keys:=keys[t:=x];
   assert a[n]!=null;
   latest:= a[n];
   assert latest!=null;
   assert latest.snd==t;
   Repr:=Repr+{a[n]};

   // assert keys==old(keys)[t:=x] && a[n].fst==x && a[n].snd==t && keys[a[n].snd]==x ;

   assert keys[a[n].snd]==x;
  assert  values ==old(values)+{t}  &&  keys==old(keys)[t:=x]  && (forall x:: x in old(values) <==> x in old( keys))&& (forall x:: x in (values) <==> x in ( keys)) ; 
//  assert MostlyValid;
//&& (forall i::1<=i<=n ==> a[i].snd in keys && keys[a[i].snd]==a[i].fst);
  // assert (forall j :: 2 <= j && j < n ==> a[j/2].getfst() <= a[j].getfst());
  // assert (forall i,j::1<=i<j<=n ==> a[i].snd!=a[j].snd);
  assert MostlyValid;
  assert (forall j :: 2 <= j && j <n  ==> a[j/2].getfst() <= a[j].getfst());
   SiftUp(n);
  assert   (forall x:: x in values <==> x in keys);
 //assert forall x:: (x in values <==>(exists i::(1<=i<=n && x==a[i].snd)));
// assert forall i,j::1<=i<j<=n ==> a[i].snd!=a[j].snd;

 assert MostlyValid;
    }

method SiftUp(k: int)
   requires 1 <= k && k <= n;
   requires (forall x:: x in values <==> x in keys);
   requires MostlyValid;
   requires (forall j :: 2 <= j && j <= n && j != k ==> a[j/2].getfst() <= a[j].getfst());
   requires (forall j :: 1 <= j && j <= n ==> j/2 != k);  // k is a leaf
   modifies a;
   
   ensures values==old(values) &&  keys==old(keys) && (forall x:: x in values <==> x in keys) ;
   ensures (forall x:: x in values <==> x in keys);
     ensures Valid;
 {
   var i := k;
   assert MostlyValid;
   while (1 < i)  
      invariant values==old(values) && keys==old(keys) && (forall x:: x in values <==> x in keys);
     invariant i <= k && MostlyValid;
    invariant (forall j :: 2 <= j && j <= n && j != i ==> a[j/2].getfst() <= a[j].getfst());
    invariant (forall j :: 1 <= j/2/2 && j/2 == i && j <= n ==> a[j/2/2].getfst() <= a[j].getfst());
   {
     if (a[i/2].getfst() <= a[i].getfst()) {
       return;
     }
     a[i/2], a[i] := a[i], a[i/2];
     i := i / 2;
   }
 }

 
method SiftUpNotLeaf(k: int)
   requires 1 <= k && k <= n;
   
   requires MostlyValid;
   requires (forall j :: 2 <= j && j <= n && j != k ==> a[j/2].getfst() <= a[j].getfst());
   requires (forall j::1<=j/2/2&& j/2==k && j<=n ==>a[j/2/2].getfst()<=a[j].getfst());
  // requires (forall j :: 1 <= j && j <= n ==> j/2 != k);  // k is a leaf
   modifies a;
   ensures Valid;
   ensures values==old(values);
   ensures keys==old(keys);
 {
   var i := k;
   assert MostlyValid;
   while (1 < i)
     invariant i <= k && MostlyValid;
     invariant (forall j :: 2 <= j && j <= n && j != i ==> a[j/2].getfst() <= a[j].getfst());
    invariant (forall j :: 1 <= j/2/2 && j/2 == i && j <= n ==> a[j/2/2].getfst() <= a[j].getfst());
   {
     if (a[i/2].getfst() <= a[i].getfst()) {
       return;
     }
     a[i/2], a[i] := a[i], a[i/2];
     i := i / 2;
   }
 }


 
method RemoveMin() returns (x: Pair<int,T>)
   requires Valid && 1 <= n;
   modifies this, a ,Repr;
  // ensures MostlyValid;
   ensures /*Valid &&*/ fresh(Repr - old(Repr));
   ensures n == old(n) - 1;
   ensures x!=null;
   //ensures x==(old (this)).min();
  // ensures values==old(values)-{x.snd} && (x.snd !in values) && keys== map i| i in old(keys) && i!=x.snd:: old(keys)[i];
   ensures MostlyValid;
   
   ensures x!=null;// && forall k:: (k in keys==>x.fst<=keys[k]);
   ensures Valid;
  
 {
  // assert 
  //assert Valid;
 // assert forall x:: (x in values <==>(exists i::(1<=i<=n && x==a[i].snd)));
   x := a[1];
   
   assert x==a[1];
   assert x!=null;
   assert x==min();
   a[1] := a[n];
  // assert x==(old (a))[1];
   //Repr:=Repr -{x};
   n := n - 1;
   values:=values-{x.snd};
   keys:=  map i| i in old(keys) && i!=x.snd:: keys[i];
   assert x.snd !in keys;
   assert x!=null;
   assert x.snd !in values;
   assert ! (exists i:: 1<=i<=n && a[i].snd ==x.snd);
  // assert forall x:: (x in values <==> exists i::i<=i<=n && a[i].snd==x);
  // assert x==a[1];
   assert (forall j :: 4 <= j && j <= n ==> a[j/2].getfst() <= a[j].getfst());
   
   SiftDown(1);
 }
 
 method SiftDown(k: int)
   requires 1 <= k;
   requires MostlyValid;
   requires (forall j :: 2 <= j && j <= n && j/2 != k ==> a[j/2].getfst() <= a[j].getfst());
   requires (forall j :: 2 <= j && j <= n && 1 <= j/2/2 && j/2/2 != k ==> a[j/2/2].getfst() <= a[j].getfst());
   // Alternatively, the line above can be expressed as:
   //     requires (forall j :: 1 <= k/2 && j/2 == k && j <= n ==> a[j/2/2] <= a[j]);
   modifies a;
   ensures keys==old(keys) && values ==old(values);
   ensures Valid;
 {
   var i := k;
   while (2*i <= n)  // while i is not a leaf
     invariant 1 <= i && MostlyValid;
     invariant (forall j :: 2 <= j && j <= n && j/2 != i ==> a[j/2].getfst() <= a[j].getfst());
     invariant (forall j :: 2 <= j && j <= n && 1 <= j/2/2 && j/2/2 != i ==> a[j/2/2].getfst() <= a[j].getfst());
   {
     var smallestChild;
     if (2*i + 1 <= n && a[2*i + 1].getfst() < a[2*i].getfst()) {
       smallestChild := 2*i + 1;
     } else {
       smallestChild := 2*i;
     }
     if (a[i].getfst() <= a[smallestChild].getfst()) {
       return;
     }
     a[smallestChild], a[i] := a[i], a[smallestChild];
     i := smallestChild;
     assert 1 <= i/2/2 ==> a[i/2/2].getfst() <= a[i].getfst();
   }
 }
 

method decreaseKey(t:T,upd:int)
requires Valid ;
modifies Repr,a;
requires forall i,j::1<=i<j<=n ==>a[i]!=a[j];
ensures Valid;
//ensures forall 

{
 var i:=n;
 while ((i>0))
 decreases i;
 invariant i>=0 &&i<=n&& MostlyValid;
 invariant  (forall x:: x in values <==> x in keys);
 invariant forall j::1<=j&&j<=n && j>i ==> ((old(a[j].fst))==a[j].fst);
 invariant forall j::1<=j&&j<=n && j<i ==> ((old(a[j].fst))==a[j].fst);
 invariant (forall j::1<=j/2/2&& j/2==i && j<=n ==>a[j/2/2].getfst()<=a[j].getfst());
 invariant (forall j :: 2 <= j && j <= n && j != i ==> a[j/2].getfst() <= a[j].getfst());
 { 
   assume upd<a[i].fst;
   if (a[i].getsnd()==t)  {                        
                             
                            
                                      
                               a[i].fst:=upd;
                               keys:=keys[a[i].snd:=upd];
                              
                            // assert (forall j::1<=j<=n && j>i ==>  a[j].fst == old(a[j].fst));  
                             assert (old(a[i].fst)>a[i].fst) && i>0;
                             assert i<=n && i>0;
                             assert (forall j::1<=j<=n && j>i ==>  a[j].fst == old(a[j].fst));
                             assert (forall j :: 2 <= j && j <= n && j != i ==> a[j/2].getfst() <= a[j].getfst());
                             assert (forall j::1<=j/2/2&& j/2==i && j<=n ==>a[j/2/2].getfst()<=a[j].getfst());
                             assert  (forall i::1<=i<=n ==> (a[i].snd in keys && keys[a[i].snd]==a[i].fst));
                             SiftUpNotLeaf(i);
                             break;}
                                                
                                                  
   else {i:=i-1;}
   
 }
 //assert Valid;
 assert (i==0==>forall j::1<=j<=n==>  a[j].fst == old(a[j].fst));
 
  
  
  
}

function method isEmpty():bool
 reads this;
 requires Valid;
 ensures Valid;
 {
   (n==0)
 }
 function method min():Pair<int,T>
 reads this;
 reads a;
 requires Valid;
 requires n>0;
 ensures Valid;
 {a[1]} 
}

class Graph {
  predicate method hasVertex(v : int) 
    reads this;
  {
    0 <= v < size
  }

  predicate Valid() 
    reads this;
  {
    |neighbors| == size &&
    (forall s :: s in neighbors[..] ==> |s| <= size) &&
    (forall i :: hasVertex(i) ==> (forall j :: j in neighbors[i] ==> 0 <= j < size && j!=i))
  }

  var neighbors: seq<seq<int>>;
  var size: nat;
  
}
class Dijkstra {
    method shortestPaths(G: Graph, source: int) returns (prev: array<int>)
        requires G != null;
        requires G.Valid;
        requires G.hasVertex(source);
        modifies this;
        requires G.size>=1;
        requires source>=0;
        //modifies PriorityQueue<int>;
        {
          
         var previous:=new int[G.size];
         var peek: Pair<int,int>;
       
         assert fresh(previous);
         // var reachables:=new int [G.size];
         // unvisited[source]:=0;
          
          var v:=G.size;
          var reachables:=new PriorityQueue<int>.Init(G.size);
          ghost var Repr:=reachables.Repr;
          ghost var latest:Pair<int,int>;
         //|G.neighbors[source]|;
          assert reachables.values=={};
          while (v>=1)
          invariant forall i:: i in reachables.values ==>i>=v && i<G.size;
          invariant forall i:: i in reachables.keys ==>i>=v&& i<G.size;
          invariant reachables.Valid;
          invariant reachables.a !=null;
          invariant reachables.n + v ==reachables.N;
          invariant reachables.N>=reachables.n;
          invariant fresh(reachables.Repr);
          invariant previous !in reachables.Repr;
          invariant  v<=G.size;
          invariant fresh(Repr-old(Repr));
            //invariant (Repr-old(Repr))!={};
          invariant  !(Repr-old(Repr)=={})==> Repr-old(Repr)=={latest};
           invariant  !(Repr-old(Repr)=={})==> latest!=null;
           invariant  !(Repr-old(Repr)=={})==> latest.snd<G.size;
           invariant forall i::i in Repr - old(Repr)==>i ==latest;
         //  invariant  forall i::i in Repr - old(Repr)==>i.snd<=G.size;
         // invariant latest.snd<=G.size;  
         // invariant  forall i:: 1<=i<=reachables.n ==>reachables.a[i]!=null && reachables.a[i].snd<G.size;
         
          {
            
            //var node:=v;
            if (v-1==source) {
              
              reachables.Insert(0,v-1);
               
              //latest:=reachables.latest;
             // assert latest!=null;
             // assert (latest.snd == v-1);
            }
            else {reachables.Insert(G.size,v-1);latest:=reachables.latest;
             // assert latest!=null;
             // assert (latest.snd == v-1);
            }
            previous[v-1]:=-1;
            Repr:=reachables.Repr;
            assert Repr!={};
            
            v:=v-1;
            }
            
          // assert Repr!={};
           //assert forall i:: i>0 && i<=reachables.n==>  (reachables.a)[i].snd< G.size;
          v:= reachables.n;
          assert forall i:: i in reachables.keys ==> i<G.size;
          while (v>0) 
          decreases v;invariant reachables.n==v;
          invariant reachables.Valid; 
          invariant fresh (reachables.Repr);
          { ghost var now_keys:=reachables.keys;
          // assert peek.snd in now_keys;
            peek:=reachables.RemoveMin();
            
           //  assert peek.snd<G.size;
            //var  neighbors_peek:= G.neighbors[peek.snd];
            
            
            v:=v-1;
              
          
          }
           
            
          }
        
          
            
     }


