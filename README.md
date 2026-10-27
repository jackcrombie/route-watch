# Route watch

Traces the path from this machine to each destination you add, once a second, and alarms when a router changes.

```bash
python3 route_watch.py
```

Open http://127.0.0.1:8765/ and add a label and an address. The list is saved in `destinations.json` next to the script. That file stays on this machine.

Requires Python 3 and `traceroute`. The page is served only on this computer.

## License

MIT. See [LICENSE](LICENSE).
