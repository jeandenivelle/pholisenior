
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

   struct clauseset
   {
      using clause = std::list< logic::term > ;

      std::list< std::list< logic::term >> set;

      clauseset( ) noexcept = default;
      clauseset( clauseset&& ) noexcept = default;
      clauseset& operator = ( clauseset&& ) noexcept = default;
         // Deleting copy.

      bool insert( const logic::term& tm ); 
         // True if insertion was successful,
         // which requires that tm is in ANF2_times.

      void res_simplify( );
         // Do a resolution simplification.
         // We look for pairs A1 \/ R1,  A2 \/ R2 where
         // A1,A2 are in conflict, and R1 is a subset of R2.
         // In that case, we remove A2. 
 
      void eq_simplify( ); 
         // Do a paramodulation simplification.
         // We look for pairs t1 == t2 \/ R1, A2[t1] \/ R2,
         // where R1 is a subset of R2. In that case,
         // we replace t1 by t2. 
         // We use KBO for directing the equality, so it can be in the
         // other direction too.

      void remove_subsumed( const logic::term& disj );
         // Remove disjunctions subsumed by disj. 

      size_t size( ) const { return set. size( ); } 
      logic::weight_type weight( ) const; 
         // Total weight of everything that we have.
  
      void print( std::ostream& out ) const;

   };


   bool inconflict( short int pol1, const logic::term& tm1,
                    short int pol2, const logic::term& tm2 );

   bool inconflict( const logic::term& tm1, const logic::term& tm2 );


   bool 
   contains( const logic::term& lit, const clauseset::clause& cls, 
             clauseset::clause::const_iterator skip );

   bool subset( const clauseset::clause& cls1, 
                clauseset::clause::const_iterator skip1,
                const clauseset::clause& cls2, 
                clauseset::clause::const_iterator skip2 );
      // True if cls1 \ skip1 is a subset of cls2 \ skip2.

   // Repeats are removed:

   logic::term
   merge( const logic::term& form1, size_t skip1,
          const logic::term& form2, size_t skip2 );

}

#endif

