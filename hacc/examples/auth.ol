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

    main {
        authenticate@Ip( credentials )
        [ authOk() ] {
            acceptToken( token )
        }
        [ authFail() ] {
            nullProcess
        }
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

    main {
        authenticate( credentials )
        if ( check@Util( credentials ) ) {
            authOk@Server()
            authOk@Client()
        } else {
            authFail@Server()
            authFail@Client()
        }
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

    main {
        [ authOk() ] {
            acceptToken@Client( makeToken@Util() )
        }
        [ authFail() ] {
            nullProcess
        }
    }
}
