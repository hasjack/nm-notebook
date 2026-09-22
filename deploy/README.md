# halfasecond.com

Static Vite build of this notebook. Old On Gravity URLs 301 to `/`.

CDN (`cdn.halfasecond.com`) is unchanged.

## Files

- Build output: rsync `dist/` → `/var/www/cdn/halfasecond/`
- Nginx: `nginx-halfasecond.conf` replaces the `:5165` proxy on `halfasecond.com`

## Cut over (needs sudo)

Files already on the box:

- site: `/var/www/cdn/halfasecond/`
- patched vhost: `/home/jack/sites-enabled-default.new`

```bash
sudo cp /etc/nginx/sites-enabled/default /etc/nginx/sites-enabled/default.bak-$(date +%F)
sudo cp /home/jack/sites-enabled-default.new /etc/nginx/sites-enabled/default
sudo nginx -t && sudo systemctl reload nginx
# optional, after a look:
# sudo docker stop halfasecond
```
