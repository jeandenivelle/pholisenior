
#ifndef LOGIC_REPLACEMENTS_
#define LOGIC_REPLACEMENTS_   

#include "term.h"
#include "outermost.h"
#include "util/print.h"

#include <vector>
#include <unordered_map>

namespace logic
{

   // The boolean should be assignend true when a 
   // replacement happened, and not changed when there was 
   // no replacement. 

   struct lifter
   {
      size_t dist;

      lifter( ) = delete;

      explicit lifter( size_t dist )
         : dist( dist )
      { }

      term operator( ) ( term t, size_t vardepth, bool& change ) const;

      void print( std::ostream& out ) const; 
   };


   // Sinker is the opposite of lifter. If term contains a 
   // DeBruijn index less than dist, we crash. 

   struct sinker
   {
      size_t dist;

      sinker( ) = delete;

      explicit sinker( size_t dist )
         : dist( dist )
      { }

      term operator( ) ( term t, size_t vardepth, bool& change ) const;

      void print( std::ostream& out ) const;
   };

   term lift( logic::term tm, size_t dist );
   term sink( logic::term tm, size_t dist );

   // A sparse subst assigns values to some, but not
   // necessarily all, De Bruijn indices. 
   // Variables that are not in the domain of the substitution,
   // are not changed.

   class sparse_subst
   {
      std::unordered_map< size_t, term > repl;

   public:
      sparse_subst( ) noexcept = default;
      sparse_subst( sparse_subst&& ) noexcept = default;
      sparse_subst& operator = ( sparse_subst&& ) = default;

      void assign( size_t var, const term& val )
         { repl. insert( std::pair( var, val )); }
      void assign( size_t var, term&& val )
         { repl. insert( std::pair( var, std::move( val ))); }

      term operator( ) ( term t, size_t vardepth, bool& change ) const;
 
      void print( std::ostream& out ) const;      
   };


   // A single subst replaces #0 by value. 

   struct singlesubst
   {
      term value; 

      singlesubst( const term& value ) 
         : value( value ) 
      { }

      term operator( ) ( term t, size_t vardepth, bool& change ) const;
      void print( std::ostream& out ) const;
   };
    
   // A fullsubst completely removes the nearest DeBruijn indices 
   // #0,#1,#2, ... 
   // DeBruijn that are not in the fullsubst are shifted down. 

   class fullsubst
   {
      std::vector< term > values;

   public:
      fullsubst( ) noexcept
      { }

      fullsubst( std::vector< term > && values ) noexcept
         : values( std::move( values ))
      { }

      term operator( ) ( term t, size_t vardepth, bool& change ) const;

      void print( std::ostream& out ) const;

      size_t size( ) const { return values. size( ); } 
      void push( term&& val ) { values. push_back( std::move( val )); }
   };

   // Argument substitution works like fullsubst, but it uses
   // the arguments of an application term. 
   // If you have a beta-redux 
   // apply( lambda ( T1, ..., Tn ) t, u1 ... um ), 
   // there is no need to construct fullsubst( u1, ..., um ).
   // Instead one can use the application term to get the ui.

   struct argsubst
   {
      term argterm;    // Term from which we take the arguments.
      size_t arity;    // In case of incomplete application, 
                       // we don't use all arguments of argterm.

      argsubst( const term& argterm, size_t arity )
         : argterm( argterm ),
           arity( arity )
      { }

      term operator( ) ( term t, size_t vardepth, bool& change ) const;

      void print( std::ostream& out ) const;
   };


   // An introsubst replaces exact names by DeBruijn indices
   // starting at #0,#1 
   // We need this substitution due to a design error in
   // class sequent. In the future, we will implement a correct
   // sequent class (strictly using DeBruin indices), and remove this class. 

   class introsubst
   {
      exact::unordered_map< size_t > map;

   public:
      introsubst( ) noexcept = default;

      void bind( exact ex );

      term operator( ) ( term t, size_t vardepth, bool& change ) const;

      size_t size( ) const { return map. size( ); }

      void print( std::ostream& out ) const;
   };

  
   // This is incomplete beta-reduction:

   struct betareduction 
   {
      size_t counter; 

      betareduction( ) noexcept
         : counter(0) 
      { }

      term operator( ) ( term t, size_t vardepth, bool& change );
         // Not const, because we count the reductions.

      void print( std::ostream& out ) const; 
   };

 
   struct rewriterule
   {
      term from;
      term to; 
     
      uint64_t counter = 0; 

      rewriterule( const term& from, const term& to )
         : from( from ), to( to ) 
      { }

      rewriterule( term&& from, term&& to )
         : from( std::move( from )),
           to( std::move( to )) 
      { }

      void swap( ) 
         { std::swap( from, to ); } 

      term operator( ) ( const term& t, size_t vardepth, bool& change );
         // Not const because of the counter.

      void print( std::ostream& out ) const;
   };

}

#endif 


