from console import Console
from .util import Util

type Msg: any { ? }
type Label: string {}

interface ClientApi {
OneWay:
    comServer( Msg ),
    leftIp,
    rightIp
}

interface IpApi {
OneWay:
    comClient( Msg )
}

interface ServerApi {
OneWay:
    ann1,
    ann2
}

service Client {
    embed Console as Console

    inputPort Input {
        location: "socket://localhost:8080"
        protocol: http { format = "json" }
        interfaces: ClientApi
    }

    outputPort Ip {
        location: "socket://localhost:8081"
        protocol: http { format = "json" }
        interfaces: IpApi
    }

    define X_Client {
        comClient@Ip( credentials )
        [ leftIp() ] {
            comServer( token )
            println@Console( "got token " + token )()
            // X_Client
        }
        [ rightIp() ] {
            println@Console( "lmao" )()
            // X_Client
            nullProcess
        }
    }

    main {
        X_Client
        X_Client
        X_Client
        X_Client
        X_Client
        X_Client
    }
}

service Ip {
    embed Util as Util

    execution: sequential

    inputPort Input {
        location: "socket://localhost:8081"
        protocol: http { format = "json" }
        interfaces: IpApi
    }

    outputPort Client {
        location: "socket://localhost:8080"
        protocol: http { format = "json" }
        interfaces: ClientApi
    }

    outputPort Server {
        location: "socket://localhost:8082"
        protocol: http { format = "json" }
        interfaces: ServerApi
    }

    define X_Ip {
        comClient( credentials )
        check@Util( credentials )( r )
        if ( r ) {
            ann1@Server()
            leftIp@Client()
            // X_Ip
        } else {
            ann2@Server()
            rightIp@Client()
            // X_Ip
        }
    }

    main {
        comClient( credentials )
        check@Util( credentials )( r )
        if ( r ) {
            ann1@Server()
            leftIp@Client()
            // X_Ip
        } else {
            ann2@Server()
            rightIp@Client()
            // X_Ip
        }
    }
}

service Server {
    embed Util as Util
    embed Console as Console

    execution: sequential

    inputPort Input {
        location: "socket://localhost:8082"
        protocol: http { format = "json" }
        interfaces: ServerApi
    }

    outputPort Client {
        location: "socket://localhost:8080"
        protocol: http { format = "json" }
        interfaces: ClientApi
    }

    define X_Server {
        [ ann1() ] {
            makeToken@Util()( r )
            comServer@Client( r )
            // X_Server
        }
        [ ann2() ] {
            // X_Server
            nullProcess
        }
    }

    main {
        [ ann1() ] {
            makeToken@Util()( r )
            comServer@Client( r )
            println@Console( "sent!" )()
            // X_Server
        }
        [ ann2() ] {
            // X_Server
            nullProcess
        }
    }
}
