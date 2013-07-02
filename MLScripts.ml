(*Exercise*)
fun less(_, nil) = nil 
|	less(n, first::L) = 
		if first < n then [first]@less(n, L)
		else less(n,L);
		
less(7, [2,4,9,6,10,12,3,19,5,7,1]);
		
(*Exercise*)
fun repeats([]) = false 
|	repeats(first::[]) = false 
|	repeats(first::second::L) =
		if first = second then true
		else repeats([second]@L);
	
repeats([1,2,3,4,5,6,7,8,9,10]);
repeats(1,2,3,4,5,6,6,7,8,9,10]);
	
(*Exercise*)
fun eval([], x) = 0.0
|	eval(L, x) =
		let
			fun helper([], x:real, n, sum:real) = sum
			|	helper(first::L, x:real, n, sum:real) =
					if n = 0 then helper(L, x, n+1, first) (*Handles constant*)
					else helper(L, x*x, n, sum + first*x);
		in
			helper(L, x:real, 0, 0.0)
		end;

(*Exercise*)
fun eval([], x) = 0.0
|	eval(L, x) =
		let
			fun helper([], x:real, n, sum:real) = sum
			|	helper(first::L, x:real, 0, sum:real) = 
					helper(L, x, 1, first) (*Handles constant*)
			|	helper(first::L, x:real, n, sum:real) = 
					helper(L, x*x, n+1, sum + first*x);
		in
			helper(L, x:real, 0, 0.0)
		end;
		
eval([1.0,5.0,3.0],2.0);
eval([7.2,6.7,4.9],3.6);
			
(*Exercise*)
fun icmp (a, b) = a < b;
fun ircmp (a, b) = a > b;
fun rcmp (a : real, b) = a < b;
fun rrcmp (a : real, b) = a > b;

fun	quicksort(nil, _) = nil (*Pg. 194*)
|	quicksort (pivot::rest, f) =
		let
			fun split(nil) = (nil,nil)
			|	split(x::xs) =
					let
						val (below, above) = split(xs)
					in
						if f(x,pivot) then (x::below, above)
						else (below, x::above)
					end;
			val (below, above) = split(rest)
		in
			quicksort(below, f) @ [pivot] @ quicksort(above, f)
		end;
	
quicksort([1,5,9,3,7,4,10,12,6], icmp);
quicksort([1,5,9,3,7,4,10,12,6], ircmp);
quicksort([1.3,5.7,9.8,3.0,7.2,4.6,10.1,12.8,6.4], rcmp);
quicksort([1.3,5.7,9.8,3.0,7.2,4.6,10.1,12.8,6.4], rrcmp);

(*Exercise*)
fun squarelist l = map(fn n => n*n) l;

(*Exercise*)
fun inclist l = fn i => map(fn n => n+i) l;

(*Exercise*)
fun bxor l = if (foldl(fn (n,c) => if n = true then c+1 else c) 0 l) mod 2 = 0 then false else true;

(*Exercise*)
fun duplist l = foldr(fn (n,c) => n::n::c) nil l;

(*Exercise*)
fun mylength l = foldl(fn (n,c) => c+1) 0 l;

(*Exercise*)
fun min l = foldl(fn (n,c) => if n < c then n else c) (hd l) (tl l);

(*Exercise*)
fun member(e, l) = foldl(fn (n,c) => if n <> e andalso c = false then false else true) false l;

(*Exercise*)
fun evens l = foldr(fn(n,c) => if (n mod 2) = 0 then n::c else c) nil l;

(*Exercise*)
fun compose l = fn arg => foldr(fn (n,c) => n(c)) arg l;

datatype number = INT of int | REAL of real;

datatype number = int | real;

fun plus (INT n) = n;

datatype number = int | real;

fun plus (INT x)(INT y) = INT (x + y) 
| plus (REAL x)(REAL y) = REAL (x + y) 
| plus (REAL x)(INT y) = REAL (x + Real.fromInt(y)) 
| plus (INT x)(REAL y) = REAL (Real.fromInt(x) + y);

fun plus n = fn i => case n of
	INT n => case i of
		INT i => n + i
		REAL i => Real.fromInt(n) + i
	REAL n => case i of
		INT i => n + Real.fromInt(i)
		REAL i => n + i;

fun plus(n:number) = fn(i:number) => 
	if INT n andalso INT i then n + i
	else if REAL n andalso REAL i then n + i
	else if INT n andalso REAL i then n + real.fromint(i)
	else real.fromint(n) + i;

fun plus(n:number) = fn(i:number) => 
	if INT n andalso INT i then n + i
	else if REAL n andalso REAL i then n + i
	else if n = int andalso i = real then n + real.fromint(i)
	else real.fromint(n) + i;
	
fun plus(n:number) = fn(i:number) => 
	if n = INT andalso i = INT then n + i
	else Real.fromInt(n) + Real.fromInt(i);
	
fun plus(n:int) = fn(i:int) => n + i
|	plus(n:real) = fn(i:real) => Real.fromInt(n) + Real.fromInt(i);

----

datatype intnest =
	INT of int |
	LIST of intnest list;

fun addup(INT n) = n
  | addup(LIST []) = 0
  | addup(LIST (n::ns)) = addup(n) + addup(LIST ns);
  
 ----
 
datatype 'data tree =
Empty |
Node of 'data tree * 'data * 'data tree;

fun appendall(Empty) = nil
|	appendall(Node(x,y,z)) =
		appendall(x)@y@appendall(z);

(*Exercise 10*)
fun isComplete(Empty) = true
|	isComplete(Node(x,y,z)) =		
		let	
			fun	binTest(Empty,Empty) = true
			|	binTest(_, Empty) = false
			|	binTest(Empty, _) = false
			|	binTest(_, _) = true
		in
			if binTest(x,z) = true then isComplete(x) andalso isComplete(z) else false
		end;
			


fun isComplete(Empty) = true
|	isComplete(Node(x,y,z)) = map
	if isComplete(x) = isComplete(z) then true else false;
	


		if isComplete(x) = false andalso isComplete(z) = false then true
		else false;

foldl(fn (isComplete(x),isComplete(z),c) => if x <> z andalso c = true then true else false) true l;
	
fun member(e, l) = foldl(fn (n,c) => if n <> e andalso c = false then false else true) false l;
	
(*Exercise*)
datatype 'a stream = Nil |
	Cons of 'a * (unit -> 'a stream);
	
fun force f = f();
	
fun printStrm _ Nil = ()
|	printStrm 0 _ = ()
|	printStrm n (Cons(x,rest)) = (
	print(Int.toString x ^ "\n");
	printStrm (n-1) (force rest)
	);

fun fib() = 
	let
		fun helper(f0, f1) = Cons(f0, fn () => helper(f1, f0+f1));
	in 
		helper(0,1)
	end;

fun halve nil = (nil, nil)
|	halve [a] = ([a], nil)
|	halve (a :: b :: cs) =
	let
		val (x, y) = halve cs
	in
		(a :: x, b :: y)
	end;
		
fun halve L =
	let
		fun helper(nil, x, y) = (x,y)
		|	helper(a::nil, x, y) = (x@[a], y)
		|	helper(a::b::rest, x, y) = helper(rest, x@[a], y@[b])
	in
		helper(L, nil, nil)
	end;

(*Exercise*)

datatype (''a, 'b) semipair = P of ''a*'b | S of ''a;

fun pairCount nil = 0
|	pairCount(P (head)::tail) = pairCount(tail) + 1
|	pairCount(S (headl)::tail) = pairCount(tail) + 0;

fun singCount nil = 0
|	singCount(P (head)::tail) = singCount(tail) + 0
|	singCount(S (headl)::tail) = singCount(tail) + 1;
	
(* First parameter is the semimap, second parameter is the desired key *)
fun hasKey nil _ = false
|	hasKey (P (x, y)::tail) key = 
		if x = key then true
		else hasKey tail key
|	hasKey (S (head)::tail) key = 
		if head = key then true
		else hasKey tail key;
		
fun getItem nil _ = NONE
|	getItem (P (x, y)::tail) key =
		if x = key then SOME(P(x, y))
		else getItem tail key
|	getItem (S (head)::tail) key =
		if head = key then SOME(S(head))
		else getItem tail key;
		
fun getValue nil key = NONE
|	getValue (P (x, y)::tail) key =
		if x = key then SOME(y)
		else getValue tail key
|	getValue(S (head)::tail) key =
		getValue tail key;
		
fun getKeys(nil) = nil
|	getKeys(P (x, y)::tail) = 
		x::getKeys(tail)
|	getKeys(S head::tail) = 
		head::getKeys tail;
		
fun getValues(nil) = nil
|	getValues(P (x,y)::tail) =
		y::getValues(tail)
|	getValues(S head::tail) =
		getValues(tail);
		
fun insertItem l p =
	let
		val original = l;
		fun helper nil (P (x,y)) = (P (x,y))::nil (*add new pair*)
		|   helper nil (S x) = (S x)::nil (*add new singleton*)
		|	helper ((P (a,b))::tail) (P (x,y)) = 
				if a = x then original (*found key*)
				else (P (a,b))::helper tail (P (x,y)) (*no match yet*)
		|	helper ((P (a,b))::tail) (S x) = 
				if a = x then original (*found key*)
				else (P (a,b))::helper tail (S x) (*no match yet*)
		|	helper ((S a)::tail) (P (x,y)) = 
				if a = x then original (*found key*)
				else (S a)::helper tail (P (x,y)) (*no match yet*)
		|	helper ((S a)::tail) (S x) = 
				if a = x then original (*found key*)
				else (S a)::helper tail (S x)(*no match yet*)
	in	
		helper l p
	end;

fun removeItem nil key = nil
|	removeItem(P (x,y)::tail) key =
		if x = key then removeItem tail key
		else (P (x,y))::removeItem tail key
|	removeItem((S x)::tail) key =
		if x = key then removeItem tail key
		else (S x)::removeItem tail key;
		
(*Statements*)
val stuff = [(P (1,"one")), S 2];
val stuff2 = [(P (1,"one")), (P (2,"two")), (P (3, "three")), S 4, S 5, S 6, (P (7, "seven"))];

pairCount stuff;
singCount stuff;
getItem stuff 1;
getItem stuff 10;
getValue stuff 1;
getValue stuff 10;
getKeys stuff;
getValues stuff;
removeItem stuff 1;
insertItem stuff (P (3,"three"));
stuff;

(*Exercise*)

fun superpower nil = 1.0
| superpower (x::rest) =
	let
		fun power(x,0.0) = 1.0
		| power (x,n) = x * power(x,n-1);
		val exp = superpower rest
	in 
		power(x,exp)
	end;
	
superpower [2.0,3.0,4.0];

(*Alternatively,*)

fun superpower nil = 1
| superpower (x::rest) =
	let
		fun power(x,0) = 1
		| power (x,n) = x * power(x,n-1);
		val exp = superpower rest
	in 
		power(x,exp)
	end;
	
superpower [2,3,4];


	