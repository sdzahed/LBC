
// DO NOT EDIT THIS FILE - it is machine generated -*- c++ -*-

#ifndef __org_omg_PortableServer_ServantLocatorOperations__
#define __org_omg_PortableServer_ServantLocatorOperations__

#pragma interface

#include <java/lang/Object.h>
#include <gcj/array.h>

extern "Java"
{
  namespace org
  {
    namespace omg
    {
      namespace PortableServer
      {
          class POA;
          class Servant;
          class ServantLocatorOperations;
        namespace ServantLocatorPackage
        {
            class CookieHolder;
        }
      }
    }
  }
}

class org::omg::PortableServer::ServantLocatorOperations : public ::java::lang::Object
{

public:
  virtual ::org::omg::PortableServer::Servant * preinvoke(JArray< jbyte > *, ::org::omg::PortableServer::POA *, ::java::lang::String *, ::org::omg::PortableServer::ServantLocatorPackage::CookieHolder *) = 0;
  virtual void postinvoke(JArray< jbyte > *, ::org::omg::PortableServer::POA *, ::java::lang::String *, ::java::lang::Object *, ::org::omg::PortableServer::Servant *) = 0;
  static ::java::lang::Class class$;
} __attribute__ ((java_interface));

#endif // __org_omg_PortableServer_ServantLocatorOperations__
