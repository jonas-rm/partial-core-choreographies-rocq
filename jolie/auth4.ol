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
    embed Util as Util

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
            println@Util( token )
            X_Client
        }
        [ rightIp() ] {
            X_Client
        }
    }

    main {
        X_Client
    }
}

service Ip {
    embed Util as Util

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
        if ( check@Util( credentials ) ) {
            ann1@Server()
            leftIp@Client()
            X_Ip
        } else {
            ann2@Server()
            rightIp@Client()
            X_Ip
        }
    }

    main {
        X_Ip
    }
}

service Server {
    embed Util as Util

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
            comServer@Client( makeToken@Util() )
            X_Server
        }
        [ ann2() ] {
            X_Server
        }
    }

    main {
        X_Server
    }
}
