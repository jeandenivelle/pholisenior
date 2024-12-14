
// Written by Hans de Nivelle September 2024.
// Made a lot of changes in December 2024.
// The main data structure now is a vector of beliefs.
// An exact name is an index into this vector.
// I merged ranking into the belief state.

#ifndef LOGIC_BELIEFSTATE_
#define LOGIC_BELIEFSTATE_  

#include <vector>
#include <unordered_map>

#include "identifier.h"
#include "exact.h"
#include "belief.h"
#include "util/print.h"

namespace logic 
{

   // Maybe I will not use this, and stick with the original ranking function:

   struct dependencies
   {
      size_t rank;
      exact::unordered_set successors;
         // Direct successors (which must have higher rank).
         // I am not sure what should be stored here. It seems more natural
         // to store predecessors, but it makes the ranking algorithm
         // less efficient. Maybe one needs two indices. 

      dependencies( ) 
         : rank(0)
      { }

      void print( std::ostream& out ) const;
   };
  
 
   class beliefstate
   {
      std::vector< std::pair< belief, dependencies >> vect; 

      using identifier2exact = 
         std::unordered_map< identifier, std::vector< exact >, 
                             identifier::hash, identifier::equal_to > ;

      identifier2exact functions;

      identifier2exact structdefs;
         // In PHOLI, an identifier can be declared as type only once, 
         // so there is no need to use a set here. Our approach
         // is that this is a problem of the type checker, not ours.
         // We are only a dumb data structure, our job is to store.
         // If we are asked to store something, we just store it without 
         // asking any questions.

      identifier2exact formulas;

      std::vector< exact > empty;
         // This is an empty vector, so that we can return
         // a reference when somebody tries to look up an identifier
         // that has no overloads. Since we always return it 
         // as a const-reference, it is harmless that it will
         // be shared.

   public:  
      beliefstate( ) noexcept = default; 
      beliefstate( beliefstate&& ) noexcept = default;
      beliefstate& operator = ( beliefstate&& ) noexcept = default;

      size_t size( ) const { return vect. size(); }

#if 0
      void add( normident id, const belief& bel )
         { add( id, belief( bel )); }
#endif

      exact append( belief&& bel );
         // If one adds a name with a pattern that overlaps with an existing
         // pattern, it will be added without complaints. It will only 
         // be detected during type checking, when the overlapping 
         // pattern is used, and causes an ambiguous overload.

      const std::vector< exact > & 
      getstructdefs( const identifier& id ) const;

      const std::vector< exact > & 
      getfunctions( const identifier& id ) const;

      std::pair< belief, dependencies > & at( exact id )
         { return vect. at( id. nr ); }

      const std::pair< belief, dependencies > & at( exact id ) const
         { return vect. at( id. nr ); } 
 
      void print( std::ostream& out ) const;
   };

}

#endif


