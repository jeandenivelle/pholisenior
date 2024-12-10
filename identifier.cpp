
#include "identifier.h"

util::hashbuilder& 
operator << ( util::hashbuilder& b, const identifier& id )
{
   std::hash< std::string > hasher; 

   for( const auto& s : id ) 
      b << hasher(s);  
   return b;
}

bool operator == ( const identifier& id1, const identifier& id2 )
{
   if( id1. size( ) != id2. size( ))
      return false;

   auto p1 = id1. begin( );
   auto p2 = id2. begin( ); 

   while( p1 != id1. end( ))
   {
      if( *p1 != *p2 ) 
         return false; 
      ++ p1; ++ p2; 
   }
   
   return true;
}

bool operator < ( const identifier& id1, const identifier& id2 ) 
{
   auto p1 = id1. begin( );
   auto p2 = id2. begin( );

   while( p1 != id1. end( ) && p2 != id2. end( )) 
   {
      if( *p1 != *p2 )
         return *p1 < *p2;
      ++ p1; ++ p2; 
   }

   return p1 == id1. end( ) && p2 != id2. end( ); 
}


std::ostream& operator << ( std::ostream& out, const identifier& id )
{
   if( id. empty( ))
      out << "(EMPTY)";
   else
   { 
      for( auto p = id. begin( ); p != id. end( ); ++ p ) 
      {
         if( p != id. begin( ))
            out << "::";
         out << *p;  
      }
   }

   return out; 
}

bool
identifier::equal_to::operator( ) ( const identifier& id1, 
                                    const identifier& id2 ) const
{
   return id1 == id2;
}

size_t identifier::hash::operator( ) ( const identifier& id ) const
{
   util::hashbuilder h; h << id; return h. val;
}

