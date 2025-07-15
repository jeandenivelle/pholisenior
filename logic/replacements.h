
#ifndef LOGIC_REPLACEMENTS_
#define LOGIC_REPLACEMENTS_   

#include "term.h"
#include "topdown.h"
#include "util/print.h"

#include <vector>
#include <unordered_map>

namespace logic
{
   // Either return a very_equal term (in simple cases 'the same term'), 
   // or a replacement.
   // The boolean should be assignend true when a replacement happened, 
   // and not changed when there was no replacement. 

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


   // A sparse subst assigns values to some, but not
   // necessarily all, De Bruijn indices. 

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


   // A letsubst stores definitions in combination with a 
   // context. 
   // The numbers inside are not De Bruijn indices, but the
   // level of the variable. 
   // In let x:T := true, y:O := whatever, the substitution will
   // (0,true), (1,whatever). Lookup needs to know the current
   // number of variables. WILL PROBABLY NOT BE USED.

   class parallelsubst
   {
      std::vector< std::pair< size_t, term >> vect; 
      size_t nrvars; 

   public:
      parallelsubst( ) noexcept
      { }

      void extend( size_t nr ) 
         { nrvars += nr; } 
            // Add variables without defining them. 

      void append( const term& val )
         { vect. push_back( std::pair( nrvars, val )); ++ nrvars; }
            // Add a variable with definition. If val contains
            // De Bruijn indices, they look back from nrvars. 

      void restore( size_t s );

      term operator( ) ( term t, size_t vardepth, bool& change ) const;

      void print( std::ostream& out ) const;
   };


   struct betareduction 
   {
      betareduction( ) = default;

      term operator( ) ( term t, size_t vardepth, bool& change ) const;

      void print( std::ostream& out ) const; 
   };

   

   struct equalitysystem
   {
      std::vector< std::pair< term, term >> sys;

      equalitysystem( ) = default;

      // Use const& or move:

      equalitysystem( const std::vector< std::pair< term, term >> & sys )
         : sys( sys )
      { }

      equalitysystem( std::vector< std::pair< term, term >> && sys )
         : sys( std::move( sys ))
      { }

      term operator( ) ( const term& t, size_t vardepth ) const;

      void print( std::ostream& out ) const;
   };

   
   struct definition
   {
      exact id;
      term val;
      
      definition( exact id, const term& val )
         : id(id), val( val )
      { }

      term operator( ) ( const term& t, size_t vardepth ) const; 

      void print( std::ostream& out ) const;
   };

   struct projection
   {



   };
}

#endif 


