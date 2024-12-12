
#include "errorstack.h"
#include <list>

void error::print( std::ostream& out ) const
{
   switch( ser )
   {
   case error::header:
      break; 

   case error::warning: 
      out << "warning: "; break;

   case error::serious: 
      out << "error: "; break;

   default: out << "??? "; break;
   }

   out << top << '\n';
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
   out << ind; vect[ pos ]. print( out );
   print( ind + 3, sub[ pos ], pos, out );   
}


