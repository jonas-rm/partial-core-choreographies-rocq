from .util import Util

type Msg: any { ? }
type Label: string {}

interface ClientApi {
OneWay:
    acceptToken( Msg ),
    authFail,
    authOk
}

interface IpApi {
OneWay:
    authenticate( Msg )
}

interface ServerApi {
OneWay:
    authFail,
    authOk
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
        authenticate@Ip( credentials )
        [ authOk() ] {
            acceptToken( token )
            X_Client
        }
        [ authFail() ] {
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
        authenticate( credentials )
        if ( check@Util( credentials ) ) {
            authOk@Server()
            authOk@Client()
            X_Ip
        } else {
            authFail@Server()
            authFail@Client()
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
        [ authOk() ] {
            acceptToken@Client( makeToken@Util() )
            X_Server
        }
        [ authFail() ] {
            X_Server
        }
    }

    main {
        X_Server
    }
}
