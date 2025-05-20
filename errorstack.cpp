
#include "errorstack.h"
#include <list>

void error::print( indentation ind, std::ostream& out ) const
{
   switch( ser )
   {
   case error::header:
      out << ind; break; 

   case error::warning: 
      out << ind << "warning: "; break;

   case error::serious: 
      out << ind << "error: "; break;

   default: out << ind << "??? "; break;
   }

   for( char c : top )
   {
      out << c;
      if( c == '\n' )
         out << ind;
   }
   out << '\n';

   reported = true;
}

void 
errorstack::print( indentation ind, 
                   size_t pos1, size_t pos2, std::ostream& out ) const
{
   std::list< size_t > errs;
      // We can access the errors only by looking backwards, but
      // we have to print them from first to last. 
      // Hence, we have to store them somewhere. We could also
      // use recursion, but that is also inefficient.
      // Lists are kind of OK I think.

   size_t p = pos2; 
   while( p > pos1 )
   {
      -- p;
      errs. push_front(p);
      p = sub[p];
   }

   for( size_t s : errs )
      print( ind, s, out );
}

void errorstack::print( indentation ind,
                        size_t pos, std::ostream& out ) const
{
   vect[ pos ]. print( ind, out );
   print( ind + 3, sub[ pos ], pos, out );   
}


