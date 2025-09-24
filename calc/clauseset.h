
#ifndef CALC_CLAUSESET_
#define CALC_CLAUSESET_

#include <list>
#include <iostream>

#include "logic/term.h"
#include "logic/cmp.h"

namespace calc
{

   // Our goal is predictability and reliability, not efficiency. 
   // This is part of the trusted core,
   // so implementation must be simple.
   // We try to keep the clause set in order for predictability.

   using clause = std::list< logic::term > ;

   struct clauseset
   {

      std::list< std::list< logic::term >> set;

      clauseset( ) noexcept = default;
      clauseset( clauseset&& ) noexcept = default;
      clauseset& operator = ( clauseset&& ) noexcept = default;
         // Deleting copy.

      void insert( const logic::term& tm ); 
         // We insert what we understand.

      uint64_t res_simplify( );
         // Do a resolution simplification.
         // We look for pairs A1 \/ R1,  A2 \/ R2 where
         // A1,A2 are in conflict, and R1 is a subset of R2.
         // In that case, we remove A2. 
 
      uint64_t eq_simplify( ); 
         // Do a paramodulation simplification.
         // We look for pairs t1 == t2 \/ R1, A2[t1] \/ R2,
         // where R1 is a subset of R2. In that case,
         // we replace t1 by t2. 
         // We use KBO for directing the equality, so it can be in the
         // other direction too.

      uint64_t fully_simplify( );
         // Keep on calling res_simplify and eq_simplify until no
         // more simplifications are possible.

      void remove_repeated( ); 
         // Remove repeated literals, and obviously false literals.

      void remove_redundant( );
         // Remove disjunctions subsumed by disj. 

      logic::term getformula( ) const;

      size_t size( ) const { return set. size( ); } 
  
      void print( std::ostream& out ) const;
   };

   bool inconflict( short int pol1, const logic::term& tm1,
                    short int pol2, const logic::term& tm2 );

   bool inconflict( const logic::term& tm1, const logic::term& tm2 );

   bool contains( const logic::term& lit, const clause& cls, 
                  clause::const_iterator skip );

   bool subset( const clause& cls1, 
                clause::const_iterator skip1,
                const clause& cls2, 
                   clause::const_iterator skip2 );
      // True if cls1 \ skip1 is a subset of cls2 \ skip2.

   bool certainly( short int pol, const logic::term& tm );
      // If pol > 0, certainly true.
      // If pol < 0, certainly false.

   void remove_repeated( clause& cls );
         // Remove repeated literals 
         // and literals that are certainly false. 

   bool istautology( const clause& cls );
      // True if we contain a literal that is certainly true. 
      // I do not expect that tautologies will occur in meaningful proofs.

   logic::term disjunction( const clause& cls );

}


#endif

