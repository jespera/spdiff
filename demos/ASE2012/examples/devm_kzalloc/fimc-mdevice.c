static int __devinit fimc_md_probe(struct platform_device *pdev)
{
	struct v4l2_device *v4l2_dev;
	struct fimc_md *fmd;
	int ret;

	fmd = devm_kzalloc(&pdev->dev, sizeof(struct fimc_md), GFP_KERNEL);
	if (!fmd)
		return -ENOMEM;

	spin_lock_init(&fmd->slock);
	fmd->pdev = pdev;

	strlcpy(fmd->media_dev.model, "SAMSUNG S5P FIMC",
		sizeof(fmd->media_dev.model));
	fmd->media_dev.link_notify = fimc_md_link_notify;
	fmd->media_dev.dev = &pdev->dev;

	v4l2_dev = &fmd->v4l2_dev;
	v4l2_dev->mdev = &fmd->media_dev;
	v4l2_dev->notify = fimc_sensor_notify;
	snprintf(v4l2_dev->name, sizeof(v4l2_dev->name), "%s",
		 dev_name(&pdev->dev));

	ret = v4l2_device_register(&pdev->dev, &fmd->v4l2_dev);
	if (ret < 0) {
		v4l2_err(v4l2_dev, "Failed to register v4l2_device: %d\n", ret);
		return ret;
	}
	ret = media_device_register(&fmd->media_dev);
	if (ret < 0) {
		v4l2_err(v4l2_dev, "Failed to register media device: %d\n", ret);
		goto err2;
	}
	ret = fimc_md_get_clocks(fmd);
	if (ret)
		goto err3;

	fmd->user_subdev_api = false;
	ret = fimc_md_register_platform_entities(fmd);
	if (ret)
		goto err3;

	if (pdev->dev.platform_data) {
		ret = fimc_md_register_sensor_entities(fmd);
		if (ret)
			goto err3;
	}
	ret = fimc_md_create_links(fmd);
	if (ret)
		goto err3;
	ret = v4l2_device_register_subdev_nodes(&fmd->v4l2_dev);
	if (ret)
		goto err3;
	ret = fimc_md_register_video_nodes(fmd);
	if (ret)
		goto err3;

	ret = device_create_file(&pdev->dev, &dev_attr_subdev_conf_mode);
	if (!ret) {
		platform_set_drvdata(pdev, fmd);
		return 0;
	}
err3:
	media_device_unregister(&fmd->media_dev);
	fimc_md_put_clocks(fmd);
	fimc_md_unregister_entities(fmd);
err2:
	v4l2_device_unregister(&fmd->v4l2_dev);
err1:
	return ret;
}
