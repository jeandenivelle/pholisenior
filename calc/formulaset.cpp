
#include "formulaset.h"
#include "logic/cmp.h"
#include <algorithm>

bool calc::formulaset::contains( const logic::term& fm ) const
{
   for( auto it = begin( ); it != end( ); ++ it )
   {
      if( logic::equal( fm, *it ))
         return true;
   }
   return false; 
}

bool calc::formulaset::insert( const logic::term& fm )
{
   if( contains( fm ))
      return false;

   repr. push_back( fm );
   return true;
}

bool calc::formulaset::insert( logic::term&& fm )
{
   if( contains( fm ))
      return false; 
   
   repr. push_back( std::move(fm) );
   return true;
}

void calc::formulaset::sort_increasing( )
{
   for( auto p = repr. begin( ); p != repr. end( ); ++ p )
   {
      logic::weight_type w = logic::weight(*p);

      auto q = p; ++ q;
      while( q != end( ))
      {
         logic::weight_type w1 = logic::weight(*q);
         if( w1 < w )
         {
            std::swap( *p, *q );
            std::swap( w, w1 );
         }
         ++ q;
      }
   }
}

void calc::formulaset::print( std::ostream& out ) const
{
   out << "{";
   for( auto p = begin( ); p != end( ); ++ p )
   {
      if( p != begin( ))
         out << ", ";
      else
         out << " ";
      out << *p;
   }
   out << " }";
}

