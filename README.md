# flocc
Flocc (Functional language on compute clusters) compiler prototype.

Web: http://www.flocc.net/
Author: Tristan Aubrey-Jones 2010
Email: developer@flocc.net

This code is a experimental prototype compiler for a data-parallel
programming language called Flocc, which stands for "Functional
language on Compute clusters". As the name suggests Flocc is a 
functional programming language, which is designed for writing
high-level data-parallel algorithms to run on clusters. 

How does it work?
Flocc programs use a simple minimal functional language (e.g., it doesn't
even support currying currently) and data-parallel operators implemented
as higher-order functions (or "combinators"), which are just functions
that take functions as arguments. Each of these data-parallel combinators
can be implemented in different ways, with different data-distributions,
on a machine with distributed-memory, like a cluster. Internally, the 
compiler therefore has multiple implementations of each high-level combinator
which distribute their inputs and outputs in different ways. The compiler
searches, considering using different implementations for each combinator
function call, and generating code (in C++ using MPI) for each. These C++
implementations are compiled, executed, and their runtime is measured.
These runtimes are fed back into the search, so that the compiler tries to
find the fastest implementation of the original program - completely automatically!

What's under the hood?
Behind the scenes the compiler uses types and type inference (very similar
to the let-polymorphic types in ML) to encode the data distributions of 
the different distributed-memory implementations of the combinators, and
to automatically synthesize approprate data distributions for candidate
implementations. When no data distribution types can be inferred, "redistribution
functions" (that perform communications like Scatter or AlltoAllv on the cluster)
are inserted to make the types unify. The search algorithms that have been most
successful in finding the fastest implementations without considering all 
possible variants, are various genetic search algorithms.
For more information please read our paper in the 
International Journal of Parallel Programming 2015 (T. Aubrey-Jones and
B. Fischer) at http://www.flocc.net/hlpp14/

The Caveats:
This code was developed for a PhD thesis (see http://www.flocc.net/thesis/),
rather than for public use, and so is a very preliminary proof of concept.
The planner currently performs and exhaustive search, and then uses the 
runtimes collected, to simulate how fast different search algorithms would
converge to find the fastest implementation, rather than actually use that 
search algorithm to find a real implementation. The back end only supports
key-value maps, and lists, and more back-end templates need to be written
to support array-based algorithms. Furthermore, unfortunately, 
the code is currently in an inconsistant state.
It was successfully used to generate code for several example programs, but 
since then the redistribution insertion code has been altered, and doesn't currently
work. This needs to be re-implemented to fully implement algorithm 2 presented
at the end of Chapter 5 of this PhD thesis. Furthermore, the current DDL type inference
algorithm (in Compiler.Types2) needs to be checked to make sure it properly conforms to the 
one given in Chapter 5. In particular, the normalization function must implement the
down-arrow algorithm in Chapter 5. If you are interested in forking, using, adapting
the code, please do get in touch by emailing developer@flocc.net.

More information:
For more information please see http://www.flocc.net/ and particularly
my PhD thesis, which explains the concepts behind Flocc, its compilation
mechanism, and implementation, in detail.

Whats in the name? 
Functional languages involve anonymous functions
called "lambda-abstractions". When run on clusters, Flocc programs 
conceptually evaluate many lambda-abstractions in parallel, and therefore
resemble a "Flocc of lambdas". (Yeah I know, it's the best I could come
up with!)
